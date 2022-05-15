//===--- VariableUpdateTracingCheck.cpp - clang-tidy ----------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "VariableUpdateTracingCheck.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/OperationKinds.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Tooling/Transformer/RangeSelector.h" // node("hoge"), name("hoge")
#include "clang/Tooling/Transformer/RewriteRule.h"
#include "clang/Tooling/Transformer/Stencil.h"
#include "llvm/ADT/StringRef.h"

#include <iostream>

namespace clang {
namespace tidy {
namespace misc {

using namespace ::clang::ast_matchers;
using namespace ::clang::transformer;

RewriteRuleWith<std::string> VariableUpdateTracingCheckImpl() {
  std::cerr << "[*] VariableUpdateTracingCheckImpl" << std::endl;

  auto declaration_found = [](auto rule_name) { return cat("Variable declaration found 📢 (", rule_name, ")"); };
  auto assignment_found = [](auto rule_name) { return cat("Assignment found 🎉 (", rule_name, ")"); };
  auto compare_found = cat("Compare found 🏆");

  // __trace_??? 関数呼び出し内ではマッチさせない
  // => マクロなので関数として認識されない！
  auto HandleTraceFunctionCall = makeRule(
    callExpr(callee(functionDecl(hasAnyName(
      "__trace_variable_declaration", 
      "__trace_variable_lvalue",
      "__trace_variable_rvalue"
    )))).bind("expr"),
    changeTo(node("expr"), cat(node("expr"))),
    cat("Trace function found 🤫")
  );

  auto capture_declrefexpr_lvalue = declRefExpr(
        to(varDecl(hasTypeLoc(typeLoc().bind("lvalue_type"))))
      ).bind("lvalue");
  auto capture_declrefexpr_rvalue = ignoringImpCasts(declRefExpr(anyOf(
        // 一時変数
        to(varDecl(hasTypeLoc(typeLoc().bind("rvalue_type")))),
        // 関数引数
        to(parmVarDecl(hasTypeLoc(typeLoc().bind("rvalue_type"))))
      )).bind("rvalue"));

/* (1)
|   |-DeclStmt 0x152bad8 <line:40:5, col:16>
|   | `-VarDecl 0x152ba08 <col:5, col:15> col:9 w 'int' cinit
|   |   `-ImplicitCastExpr 0x152bac0 <col:13, col:15> 'int' <LValueToRValue>
|   |     `-MemberExpr 0x152ba90 <col:13, col:15> 'int' lvalue .b 0x152af30
|   |       `-DeclRefExpr 0x152ba70 <col:13> 'struct pair':'struct pair' lvalue Var 0x152b570 'p' 'struct pair':'struct pair'
*/
/* (2)
|   |-DeclStmt 0x1e5a358 <line:60:5, col:34>
|   | `-VarDecl 0x1e5a240 <col:5, col:28> col:9 length 'int' cinit
|   |   `-ImplicitCastExpr 0x1e5a340 <col:18, col:28> 'int' <LValueToRValue>
|   |     `-MemberExpr 0x1e5a310 <col:18, col:28> 'int' lvalue .length 0x1e59a78
|   |       `-MemberExpr 0x1e5a2e0 <col:18, col:21> 'struct (unnamed struct at bad.c:51:5)':'struct header::(unnamed at bad.c:51:5)' lvalue ->nested 0x1e59b28
|   |         `-ImplicitCastExpr 0x1e5a2c8 <col:18> 'struct header *' <LValueToRValue>
|   |           `-DeclRefExpr 0x1e5a2a8 <col:18> 'struct header *' lvalue Var 0x1e5a090 'h' 'struct header *'
*/
/* (3)
|   |-DeclStmt 0x186ad90 <line:65:5, col:39>
|   | `-VarDecl 0x186ac48 <col:5, col:34> col:9 value 'int' cinit
|   |   `-ImplicitCastExpr 0x186ad78 <col:17, col:34> 'int' <LValueToRValue>
|   |     `-MemberExpr 0x186ad48 <col:17, col:34> 'int' lvalue .value 0x1869d88
|   |       `-MemberExpr 0x186ad18 <col:17, col:27> 'struct (unnamed struct at bad.c:54:9)':'struct header::(unnamed at bad.c:54:9)' lvalue .nested 0x1869e38
|   |         `-MemberExpr 0x186ace8 <col:17, col:20> 'struct (unnamed struct at bad.c:52:5)':'struct header::(unnamed at bad.c:52:5)' lvalue ->nested 0x1869ee8
|   |           `-ImplicitCastExpr 0x186acd0 <col:17> 'struct header *' <LValueToRValue>
|   |             `-DeclRefExpr 0x186acb0 <col:17> 'struct header *' lvalue Var 0x186a950 'h' 'struct header *'
*/
/* (3)
|   |-BinaryOperator 0x132a068 <line:69:5, col:30> 'int' '='
|   | |-DeclRefExpr 0x1329f68 <col:5> 'int' lvalue Var 0x1329d38 'value' 'int'
|   | `-ImplicitCastExpr 0x132a050 <col:13, col:30> 'int' <LValueToRValue>
|   |   `-MemberExpr 0x132a020 <col:13, col:30> 'int' lvalue .value 0x1328f88
|   |     `-MemberExpr 0x1329ff0 <col:13, col:23> 'struct (unnamed struct at bad.c:55:9)':'struct header::(unnamed at bad.c:55:9)' lvalue .nested 0x1329038
|   |       `-MemberExpr 0x1329fc0 <col:13, col:16> 'struct (unnamed struct at bad.c:53:5)':'struct header::(unnamed at bad.c:53:5)' lvalue ->nested 0x13290e8
|   |         `-ImplicitCastExpr 0x1329fa8 <col:13> 'struct header *' <LValueToRValue>
|   |           `-DeclRefExpr 0x1329f88 <col:13> 'struct header *' lvalue Var 0x1329b70 'h' 'struct header *'
*/
  auto __capture_record_type = ignoringImpCasts(declRefExpr(to(varDecl(hasTypeLoc(typeLoc().bind("record_type"))))));
  auto capture_record_type = anyOf(
      // /* (1) */ __capture_record_type,
      /* (1) */ memberExpr(has(__capture_record_type)),
      /* (2) */ memberExpr(has(memberExpr(has(__capture_record_type)))),
      /* (3) */ memberExpr(has(memberExpr(has(memberExpr(has(__capture_record_type))))))
    );
  auto capture_memberexpr_lvalue = memberExpr(
      member(fieldDecl(hasTypeLoc(typeLoc().bind("lvalue_type")))),
      capture_record_type
    ).bind("lvalue");
  auto capture_memberexpr_rvalue = memberExpr(
      member(fieldDecl(hasTypeLoc(typeLoc().bind("rvalue_type")))),
      capture_record_type
    ).bind("rvalue");

  auto capture_declstmt = hasParent(varDecl(
      hasParent(declStmt( // 文法破壊防止
        unless(hasParent(forStmt())),
        hasSingleDecl(varDecl())
      ).bind("DeclStmt")),
      hasTypeLoc(typeLoc().bind("lvalue_type"))
    ).bind("lvalue"));

  auto change_lvalue = changeTo(
      node("lvalue"), 
      cat(
        "__trace_variable_lvalue(", node("lvalue"), ", ", node("lvalue_type"), ")"
      )
    );
  auto change_rvalue = changeTo(
      node("rvalue"), 
      cat(
        "__trace_variable_rvalue(", node("rvalue"), ", ", node("rvalue_type"), ")"
      )
    );
  auto change_rvalue_const_int = changeTo(
      node("rvalue"), 
      cat(
        "__trace_variable_rvalue(", node("rvalue"), ", ", "const int", ")"
      )
    );
  auto change_member_lvalue = changeTo(
      node("lvalue"), 
      cat(
        "__trace_member_lvalue(", node("lvalue"), ", ", name("lvalue_type"), ", ", node("record_type"), ")"
      )
    );
  auto change_declstmt = changeTo(
    after(node("DeclStmt")),
    cat(" __trace_variable_declaration(", name("lvalue"), ", ", node("lvalue_type"), ");")
  );

  // <DeclStmt>
  // 初期化パターンを網羅するのが難しい。特に構造体やループの中の変数宣言
  // FIXME: 2つ目の変数を拾えてない
  // FIXME: 初期化に使っている値を拾えてない
/*
|   |-DeclStmt 0x19db570 <line:42:5, col:13>
|   | |-VarDecl 0x19da3d0 <col:5, col:9> col:9 used x 'int'
|   | `-VarDecl 0x19db4f0 <col:5, col:12> col:12 used y 'int'
*/
  // auto HandleDeclStmt = makeRule(
  //   declStmt(
  //     unless(hasParent(forStmt())), // 文法破壊防止
  //     forEach(varDecl(
  //       hasTypeLoc(typeLoc().bind("lvalue_type"))
  //     ).bind("lvalue"))
  //   ).bind("insert_point"),
  //   {},
  //   declaration_found("HandleDeclStmt")
  // );

/*
|   |-DeclStmt 0x14a25f8 <line:29:5, col:14>
|   | `-VarDecl 0x14a2558 <col:5, col:13> col:9 used z 'int' cinit
|   |   `-ImplicitCastExpr 0x14a25e0 <col:13> 'int' <LValueToRValue>
|   |     `-DeclRefExpr 0x14a25c0 <col:13> 'int' lvalue Var 0x14a2308 'x' 'int'
*/
  // <VarDecl <DeclRefExpr>>
  auto HandleRefExprVarDecl = makeRule(
      declRefExpr(
        hasParent(implicitCastExpr(
          capture_declstmt
        )),
        to(varDecl(hasTypeLoc(typeLoc().bind("rvalue_type"))))
      ).bind("rvalue"),
      {
        change_declstmt,
        change_rvalue,
      },
      declaration_found("HandleRefExprVarDecl")
    );

  // <VarDecl <IntegerLiteral>>
/*
    |-DeclStmt 0x157d1b0 <line:52:5, col:14>
    | `-VarDecl 0x157d128 <col:5, col:13> col:9 used x 'int' cinit
    |   `-IntegerLiteral 0x157d190 <col:13> 'int' 3
*/
  auto HandleIntegerLiteralVarDecl = makeRule(
      expr(integerLiteral(
        capture_declstmt
      )).bind("rvalue"),
      {
        change_declstmt,
        change_rvalue_const_int,
      },
      declaration_found("HandleIntegerLiteralVarDecl")
    );

  // <VarDecl <MemberExpr <DeclRefExpr>>>
  auto HandleRvalueMemberExprVarDecl = makeRule(
      expr(
        hasParent(implicitCastExpr(
          capture_declstmt
        )),
        capture_memberexpr_rvalue
      ),
      {
        change_declstmt,
        changeTo(
          node("rvalue"), 
          cat(
            "__trace_member_rvalue(", node("rvalue"), ", ", name("rvalue_type"), ", ", node("record_type"), ")"
          )
        ), 
      },
      assignment_found("HandleRvalueMemberExprVarDecl")
    );

  // TODO: <VarDecl <CallExpr>>
  // NOTE: 関数の戻り値をトラックすれば省略可能

  // TODO: <VarDecl <UnaryOperator <DeclRefExpr>>>

  // <AssingnOperator <DeclRefExpr> <???>>
  // lvalue をハンドルするのみ
  auto HandleLvalueDeclRefExprAssignment = makeRule(
      expr(
        hasParent(binaryOperator(isAssignmentOperator())),
        capture_declrefexpr_lvalue
      ),
      change_lvalue,
      assignment_found("HandleLvalueDeclRefExprAssignment")
    );

  // <MemberExpr> = <???>
  // lvalue をハンドルするのみ
  auto HandleLvalueMemberExprAssignment = makeRule(
      expr(
        hasParent(binaryOperator(isAssignmentOperator())),
        capture_memberexpr_lvalue
      ),
      change_member_lvalue,
      assignment_found("HandleLvalueMemberExprAssignment")
    );

  // <???> = <DeclRefExpr>;
  // rvalue をハンドルするのみ
  auto HandleRvalueDeclRefExprAssignment = makeRule(
      // TODO: v += u を v = v + u に正規化
      expr(
        hasParent(binaryOperator(isAssignmentOperator())),
        capture_declrefexpr_rvalue
      ),
      change_rvalue,
      assignment_found("HandleRvalueDeclRefExprAssignment")
    );

  // <???> = <IntegerLiteral>
  // <???> ?= <IntegerLiteral>
  // rvalue をハンドルするのみ
/*
|   |-BinaryOperator 0x20156d0 <line:45:5, col:12> 'int' '='
|   | |-MemberExpr 0x2015680 <col:5, col:8> 'int' lvalue ->b 0x20104c0
|   | | `-ImplicitCastExpr 0x2015668 <col:5> 'struct pair *' <LValueToRValue>
|   | |   `-DeclRefExpr 0x2015648 <col:5> 'struct pair *' lvalue Var 0x2014300 'q' 'struct pair *'
|   | `-IntegerLiteral 0x20156b0 <col:12> 'int' 1
*/
  auto HandleRvalueLiteralAssignment = makeRule(
      // TODO: v += u を v = v + u に正規化
      expr(
        hasParent(binaryOperator(
          anyOf(
            isAssignmentOperator(),
            hasAnyOperatorName("+=", "-=")
          )
        )),
        integerLiteral()
      ).bind("rvalue"),
      change_rvalue_const_int,
      assignment_found("HandleRvalueLiteralAssignment")
    );

  // <DeclRefExpr>++
/*
|     |-UnaryOperator 0xcbd3d0 <col:28, col:29> 'int' postfix '++'
|     | `-DeclRefExpr 0xcbd3b0 <col:28> 'int' lvalue Var 0xcbc1e8 'i' 'int'
*/
  auto HandleRvalueLiteralUnaryOperator = makeRule(
      unaryOperator(
        hasOperatorName("++"),
        has(capture_declrefexpr_lvalue)
      ).bind("expr"),
      changeTo(
        node("expr"),
        cat(
          "__trace_variable_lvalue(", node("lvalue"), ", ", node("lvalue_type"), ")"
          " += ",
          "__trace_variable_rvalue(1, const int)"
        )
      ),
      cat("<DeclRefExpr>++ found")
    );

  // <???> = <MemberExpr <DeclRefExpr>>
  // rvalue をハンドルするのみ
/*
|   `-BinaryOperator 0x1a9ea80 <line:47:5, col:15> 'int' '='
|     |-MemberExpr 0x1a9e9d0 <col:5, col:8> 'int' lvalue ->a 0x1a99528
|     | `-ImplicitCastExpr 0x1a9e9b8 <col:5> 'struct pair *' <LValueToRValue>
|     |   `-DeclRefExpr 0x1a9e998 <col:5> 'struct pair *' lvalue Var 0x1a9d3d0 'q' 'struct pair *'
|     `-ImplicitCastExpr 0x1a9ea68 <col:12, col:15> 'int' <LValueToRValue>
|       `-MemberExpr 0x1a9ea38 <col:12, col:15> 'int' lvalue ->b 0x1a99590
|         `-ImplicitCastExpr 0x1a9ea20 <col:12> 'struct pair *' <LValueToRValue>
|           `-DeclRefExpr 0x1a9ea00 <col:12> 'struct pair *' lvalue Var 0x1a9d3d0 'q' 'struct pair *'
*/
  auto HandleRvalueMemberExprAssignment = makeRule(
      // TODO: v += u を v = v + u に正規化
      expr(
        hasParent(implicitCastExpr(
          hasParent(binaryOperator(isAssignmentOperator()))
        )),
        capture_memberexpr_rvalue
      ),
      changeTo(
        node("rvalue"), 
        cat(
          "__trace_member_rvalue(", node("rvalue"), ", ", name("rvalue_type"), ", ", node("record_type"), ")"
        )
      ), 
      assignment_found("HandleRvalueMemberExprAssignment")
    );

  // <BinaryOperator <DeclRefExpr> ...>
  // rvalue のみchangeTo
  // TODO: HandleCompareOperator が優先されてこのルールによるfixが無視される
  auto HandleRvalueDeclRefExprBinaryOperator = makeRule(
      declRefExpr(
        hasParent(implicitCastExpr(
          hasParent(binaryOperator(unless(isAssignmentOperator())))
        )),
        to(varDecl(hasTypeLoc(typeLoc().bind("rvalue_type"))))
      ).bind("rvalue"),
      change_rvalue,
      assignment_found("HandleRvalueDeclRefExprBinaryOperator")
    );

/*
|   `-DeclStmt 0x8cc178 <line:37:5, col:22>
|     `-VarDecl 0x8cc020 <col:5, col:21> col:9 z 'int' cinit
|       `-BinaryOperator 0x8cc158 <col:13, col:21> 'int' '+'
|         |-ImplicitCastExpr 0x8cc128 <col:13, col:15> 'int' <LValueToRValue>
|         | `-MemberExpr 0x8cc0a8 <col:13, col:15> 'int' lvalue .a 0x8c8548
|         |   `-DeclRefExpr 0x8cc088 <col:13> 'struct pair':'struct pair' lvalue Var 0x8cb9a0 'p' 'struct pair':'struct pair'
|         `-ImplicitCastExpr 0x8cc140 <col:19, col:21> 'int' <LValueToRValue>
|           `-MemberExpr 0x8cc0f8 <col:19, col:21> 'int' lvalue .b 0x8c85b0
|             `-DeclRefExpr 0x8cc0d8 <col:19> 'struct pair':'struct pair' lvalue Var 0x8cb9a0 'p' 'struct pair':'struct pair'
*/
  auto HandleRvalueMemberExprBinaryOperator = makeRule(
      expr(
        hasParent(implicitCastExpr(
          hasParent(binaryOperator(unless(isAssignmentOperator())))
        )),
        capture_memberexpr_rvalue
      ),
      change_rvalue,
      assignment_found("HandleRvalueMemberExprBinaryOperator")
    );

  // <BinaryOperator <IntegerLiteral> ...>
  auto HandleRvalueBinaryOperatorIntegerLiteralBinaryOperator = makeRule(
      expr(integerLiteral(
        hasParent(binaryOperator(unless(isAssignmentOperator())))
      )).bind("rvalue"),
      change_rvalue_const_int,
      assignment_found("HandleRvalueBinaryOperatorIntegerLiteralBinaryOperator")
    );

  // TODO: 構造体メンバーへのアクセスありのBinaryOperator
  // TODO: 関数呼び出しありの代入

  // <BinaryOperator <DeclRefExpr> ...>
  auto HandleCompareOperator = makeRule(
      binaryOperator(anyOf(
        isComparisonOperator(),
        hasAnyOperatorName("||", "&&")
      )).bind("expr"),
      changeTo(
        node("expr"), 
        cat(
          "__trace_condition(", node("expr"), ")"
        )
      ),
      compare_found
    );

  // <ReturnStmt <DeclRefExpr>>
  auto HandleDeclRefExprReturnStmt = makeRule(
      returnStmt(hasReturnValue(ignoringImpCasts(declRefExpr(
        to(varDecl(hasTypeLoc(typeLoc().bind("rvalue_type"))))
      ).bind("rvalue")))),
      change_rvalue,
      cat("Function return statement found 📢")
    );

  // <ReturnStmt <IntegerLiteral>>
  auto HandleIntegerLiteralReturnStmt = makeRule(
      returnStmt(hasReturnValue(expr(integerLiteral()).bind("rvalue"))),
      change_rvalue_const_int,
      cat("Function return statement found 📢")
    );

  // TODO: <ReturnStmt <BinaryOperation>>

  // TODO: <ReturnStmt <構造体>>
/*
|   `-ReturnStmt 0x8c5440 <line:29:5, col:19>
|     `-ImplicitCastExpr 0x8c5428 <col:12, col:19> 'int' <LValueToRValue>
|       `-MemberExpr 0x8c53f8 <col:12, col:19> 'int' lvalue ->result 0x8c4c30
|         `-ImplicitCastExpr 0x8c53e0 <col:12> 'struct Param *' <LValueToRValue>
|           `-DeclRefExpr 0x8c53c0 <col:12> 'struct Param *' lvalue ParmVar 0x8c4d30 'param' 'struct Param *'
*/

  return applyFirst({
    HandleTraceFunctionCall, // 無意味
    HandleRefExprVarDecl,
    HandleRvalueMemberExprVarDecl,
    HandleIntegerLiteralVarDecl,
    HandleLvalueDeclRefExprAssignment,
    HandleLvalueMemberExprAssignment,
    HandleRvalueDeclRefExprAssignment,
    HandleRvalueLiteralAssignment,
    HandleRvalueLiteralUnaryOperator,
    HandleRvalueMemberExprAssignment,
    HandleRvalueDeclRefExprBinaryOperator,
    HandleRvalueMemberExprBinaryOperator,
    HandleRvalueBinaryOperatorIntegerLiteralBinaryOperator,
    HandleCompareOperator,
    HandleDeclRefExprReturnStmt,
    HandleIntegerLiteralReturnStmt,
  });
}

VariableUpdateTracingCheck::VariableUpdateTracingCheck(StringRef Name,
                                               ClangTidyContext *Context)
    : utils::TransformerClangTidyCheck(VariableUpdateTracingCheckImpl(), Name, Context) {}

} // namespace misc
} // namespace tidy
} // namespace clang
