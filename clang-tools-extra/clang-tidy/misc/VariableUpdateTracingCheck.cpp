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

  auto declaration_found = cat("Variable declaration found 📢");
  auto assignment_found = cat("Assignment found 🎉");
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
  auto capture_declrefexpr_rvalue = hasRHS(ignoringImpCasts(
      declRefExpr(anyOf(
        // 一時変数
        to(varDecl(hasTypeLoc(typeLoc().bind("rvalue_type")))),
        // 関数引数
        to(parmVarDecl(hasTypeLoc(typeLoc().bind("rvalue_type"))))
      )).bind("rvalue")
    ));

  auto capture_memberexpr_lvalue = hasLHS(
      memberExpr(
        member(fieldDecl(hasTypeLoc(typeLoc().bind("lvalue_type")))),
        has(declRefExpr(to(varDecl(hasTypeLoc(typeLoc().bind("record_type"))))))
      ).bind("lvalue")
    );
  auto capture_memberexpr_rvalue = memberExpr(
        member(fieldDecl(hasTypeLoc(typeLoc().bind("rvalue_type")))),
        has(declRefExpr(to(varDecl(hasTypeLoc(typeLoc().bind("record_type"))))))
      ).bind("rvalue");

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

  // <DeclStmt>
  // 初期化パターンを網羅するのが難しい。特に構造体やループの中の変数宣言
  auto HandleDeclStmt = makeRule(
    declStmt(
      unless(hasParent(forStmt())), // 文法破壊防止
      hasSingleDecl(varDecl(
        hasTypeLoc(typeLoc().bind("lvalue_type"))
      ).bind("lvalue"))
    ),
    {
      // 右辺の書き換えは別のルールに任せる
      changeTo(
        after(node("lvalue")),
        cat(
          " __trace_variable_declaration(", name("lvalue"), ", ", node("lvalue_type"), ");"
        )
      ),
    },
    declaration_found
  );

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
          hasParent(varDecl())
        )),
        to(varDecl(hasTypeLoc(typeLoc().bind("rvalue_type"))))
      ).bind("rvalue"),
      change_rvalue,
      declaration_found
    );

  // <VarDecl <IntegerLiteral>>
/*
    |-DeclStmt 0x157d1b0 <line:52:5, col:14>
    | `-VarDecl 0x157d128 <col:5, col:13> col:9 used x 'int' cinit
    |   `-IntegerLiteral 0x157d190 <col:13> 'int' 3
*/
  auto HandleIntegerLiteralVarDecl = makeRule(
      expr(integerLiteral(
        hasParent(varDecl())
      )).bind("rvalue"),
      change_rvalue_const_int,
      declaration_found
    );

/*
|   |-DeclStmt 0x152bad8 <line:40:5, col:16>
|   | `-VarDecl 0x152ba08 <col:5, col:15> col:9 w 'int' cinit
|   |   `-ImplicitCastExpr 0x152bac0 <col:13, col:15> 'int' <LValueToRValue>
|   |     `-MemberExpr 0x152ba90 <col:13, col:15> 'int' lvalue .b 0x152af30
|   |       `-DeclRefExpr 0x152ba70 <col:13> 'struct pair':'struct pair' lvalue Var 0x152b570 'p' 'struct pair':'struct pair'
*/
  // <VarDecl <MemberExpr <DeclRefExpr>>>
  auto HandleRvalueMemberExprVarDecl = makeRule(
      expr(
        hasParent(implicitCastExpr(hasParent(varDecl()))),
        capture_memberexpr_rvalue
      ),
      {
        changeTo(
          node("rvalue"), 
          cat(
            "__trace_member_rvalue(", node("rvalue"), ", ", name("rvalue_type"), ", ", node("record_type"), ")"
          )
        ), 
      },
      assignment_found
    );

  // <VarDecl <CallExpr>>
  // NOTE: 関数の戻り値をトラックすれば省略可能

  // <DeclRefExpr> = <DeclRefExpr>;
  auto HandleRvalueDeclRefExprAssignment = makeRule(
      // TODO: v += u を v = v + u に正規化
      binaryOperator(
        isAssignmentOperator(),
        hasLHS(capture_declrefexpr_lvalue),
        capture_declrefexpr_rvalue
      ),
      {
        change_lvalue,
        change_rvalue,
      },
      assignment_found
    );

  // <DeclRefExpr> = <IntegerLiteral>
  // <DeclRefExpr> ?= <IntegerLiteral>
  auto HandleRvalueLiteralAssignment = makeRule(
      // TODO: v += u を v = v + u に正規化
      binaryOperator(
        anyOf(
          isAssignmentOperator(),
          hasAnyOperatorName("+=", "-=")
        ),
        hasLHS(capture_declrefexpr_lvalue),
        hasRHS(
          expr(integerLiteral()).bind("rvalue")
        )
      ),
      {
        change_lvalue,
        change_rvalue_const_int,
      },
      assignment_found
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

  // <DeclRefExpr> = <MemberExpr <DeclRefExpr>>
  auto HandleRvalueMemberExprAssignment = makeRule(
      // TODO: v += u を v = v + u に正規化
      binaryOperator(
        isAssignmentOperator(),
        hasLHS(capture_declrefexpr_lvalue),
        hasRHS(capture_memberexpr_rvalue)
      ),
      {
        change_lvalue,
        changeTo(
          node("rvalue"), 
          cat(
            "__trace_member_rvalue(", node("rvalue"), ", ", name("rvalue_type"), ", ", node("record_type"), ")"
          )
        ), 
      },
      assignment_found
    );

  // <MemberExpr <DeclRefExpr>> = <DeclRefExpr>
/*
|   |-BinaryOperator 0x8c5390 <line:28:5, col:31> 'int' '='
|   | |-MemberExpr 0x8c5258 <col:5, col:12> 'int' lvalue ->result 0x8c4c30
|   | | `-ImplicitCastExpr 0x8c5240 <col:5> 'struct Param *' <LValueToRValue>
|   | |   `-DeclRefExpr 0x8c5220 <col:5> 'struct Param *' lvalue ParmVar 0x8c4d30 'param' 'struct Param *'
*/
  auto HandleLvalueMemberExprRvalueDeclRefExprAssignment = makeRule(
      binaryOperator(
        isAssignmentOperator(),
        capture_memberexpr_lvalue,
        capture_declrefexpr_rvalue
      ),
      {
        changeTo(
          node("lvalue"), 
          cat(
            "__trace_member_lvalue(", node("lvalue"), ", ", name("lvalue_type"), ", ", node("record_type"), ")"
          )
        ),
        change_rvalue, 
      },
      assignment_found
    );

  // <MemberExpr <DeclRefExpr>> = <IntegerLiteral>
  auto HandleLvalueMemberExprRvalueIntegerLiteralAssignment = makeRule(
      // TODO: v += u を v = v + u に正規化
      binaryOperator(
        isAssignmentOperator(),
        capture_memberexpr_lvalue,
        hasRHS(
          expr(integerLiteral()).bind("rvalue")
        )
      ),
      {
        changeTo(
          node("lvalue"), 
          cat(
            "__trace_member_lvalue(", node("lvalue"), ", ", name("lvalue_type"), ", ", node("record_type"), ")"
          )
        ),
        change_rvalue_const_int, 
      },
      assignment_found
    );

  // TODO: <MemberExpr <DeclRefExpr>> = <MemberExpr <DeclRefExpr>>

  // <BinaryOperator <DeclRefExpr> ...>
  // TODO: HandleCompareOperator が優先されてこのルールによるfixが無視される
  auto HandleRvalueBinaryOperatorDeclRefExprBinaryOperator = makeRule(
      declRefExpr(
        hasParent(implicitCastExpr(
          hasParent(binaryOperator(unless(isAssignmentOperator())))
        )),
        to(varDecl(hasTypeLoc(typeLoc().bind("rvalue_type"))))
      ).bind("rvalue"),
      change_rvalue,
      assignment_found
    );

  // <BinaryOperator <IntegerLiteral> ...>
  auto HandleRvalueBinaryOperatorIntegerLiteralBinaryOperator = makeRule(
      expr(integerLiteral(
        hasParent(binaryOperator(unless(isAssignmentOperator())))
      )).bind("rvalue"),
      change_rvalue_const_int,
      assignment_found
    );

  // TODO: 構造体メンバーへのアクセスありのBinaryOperator
  // TODO: 関数呼び出しありの代入

  // <BinaryOperator <DeclRefExpr> ...>
  auto HandleCompareOperator = makeRule(
      binaryOperator(isComparisonOperator()).bind("expr"),
      changeTo(
        node("expr"), 
        cat(
          "__trace_compare(", node("expr"), ")"
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
    HandleDeclStmt,
    HandleRefExprVarDecl,
    HandleRvalueMemberExprVarDecl,
    HandleIntegerLiteralVarDecl,
    HandleRvalueDeclRefExprAssignment,
    HandleRvalueLiteralAssignment,
    HandleRvalueLiteralUnaryOperator,
    HandleRvalueMemberExprAssignment,
    HandleLvalueMemberExprRvalueDeclRefExprAssignment,
    HandleLvalueMemberExprRvalueIntegerLiteralAssignment,
    HandleRvalueBinaryOperatorDeclRefExprBinaryOperator,
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
