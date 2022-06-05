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
#include "clang/Tooling/Transformer/RewriteRule.h" // changeTo(), addInclude()
#include "clang/Tooling/Transformer/Stencil.h"
#include "llvm/ADT/StringRef.h"

#include <iostream>

namespace clang {
namespace ast_matchers {

AST_MATCHER(VarDecl, isRegister) {
  return Node.getStorageClass() == SC_Register;
}

AST_MATCHER(Expr, isInMacro) {
  return Node.getBeginLoc().isMacroID();
}

} // namespace clang
} // namespace ast_matchers

namespace clang {
namespace tidy {
namespace misc {

using namespace ::clang::ast_matchers;
using namespace ::clang::transformer;

RewriteRuleWith<std::string> VariableUpdateTracingCheckImpl() {
  std::cerr << "[*] VariableUpdateTracingCheckImpl" << std::endl;

  auto declaration_found = [](auto rule_name) { return cat("Variable declaration found 📢 (", rule_name, ")"); };
  auto assignment_found = [](auto rule_name) { return cat("Assignment found 🎉 (", rule_name, ")"); };
  auto return_found = [](auto rule_name) { return cat("Return statement found 📢 (", rule_name, ")"); };
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

/* (a) 
|   |-DeclStmt 0x1b86a20 <line:105:5, col:19>
|   | `-VarDecl 0x1b869b8 <col:5, col:18> col:18 used i 'int' register
*/
  auto capture_declrefexpr_lvalue = declRefExpr(
        to(varDecl(
          /* (a) */ unless(isRegister()),
          hasTypeLoc(typeLoc().bind("lvalue_type"))
        ))
      ).bind("lvalue");
  auto capture_declrefexpr_rvalue = ignoringImpCasts(declRefExpr(anyOf(
        // 一時変数
        to(varDecl(unless(isRegister()), hasTypeLoc(typeLoc().bind("rvalue_type")))),
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

  auto capture_declstmt = varDecl(
      hasParent(declStmt( // 文法破壊防止
        unless(hasParent(forStmt())),
        hasSingleDecl(varDecl())
      ).bind("DeclStmt")),
      hasTypeLoc(typeLoc().bind("lvalue_type"))
    ).bind("lvalue");

  auto capture_assign_operator = binaryOperator(
      anyOf(
        isAssignmentOperator(),
        hasAnyOperatorName("+=", "-=")
      )
    );

/* バグる例：
    char *element, *end;
    __trace_variable_lvalue(end, char *element, *) = (char *)base + *nmemb * __trace_variable_rvalue(size, size_t);
                                       ~~~~~~~~~~ 型じゃない
*/
  auto change_lvalue = changeTo(
      node("lvalue"), 
      cat(
        "__trace_variable_lvalue(", node("lvalue"), ", (", node("lvalue_type"), "))"
      )
    );
  auto change_rvalue = changeTo(
      node("rvalue"), 
      cat(
        "__trace_variable_rvalue(", node("rvalue"), ", (", node("rvalue_type"), "))"
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
        "__trace_member_lvalue(", node("lvalue"), ", (", node("lvalue_type"), "), (", node("record_type"), "))"
      )
    );
  auto change_declstmt = changeTo(
    after(node("DeclStmt")),
    cat(" __trace_variable_declaration(", name("lvalue"), ", (", node("lvalue_type"), "));")
  );

  auto add_include = addInclude("trace.h", IncludeFormat::Angled);

/* (1)
|   |-DeclStmt 0x14a25f8 <line:29:5, col:14>
|   | `-VarDecl 0x14a2558 <col:5, col:13> col:9 used z 'int' cinit
|   |   `-ImplicitCastExpr 0x14a25e0 <col:13> 'int' <LValueToRValue>
|   |     `-DeclRefExpr 0x14a25c0 <col:13> 'int' lvalue Var 0x14a2308 'x' 'int'
*/
/* (2)
|   |-DeclStmt 0xc216d8 <line:24:5, col:38>
|   | `-VarDecl 0xc215f8 <col:5, col:37> col:18 used z 'unsigned int' cinit
|   |   `-CStyleCastExpr 0xc216b0 <col:22, col:37> 'unsigned int' <IntegralCast>
|   |     `-ImplicitCastExpr 0xc21698 <col:37> 'int' <LValueToRValue> part_of_explicit_cast
|   |       `-DeclRefExpr 0xc21660 <col:37> 'int' lvalue Var 0xc1e730 'x' 'int'
*/
  // <VarDecl <DeclRefExpr>>
  auto HandleRefExprVarDecl = makeRule(
      declRefExpr(
        anyOf(
          /* (1) */ hasParent(implicitCastExpr(hasParent(capture_declstmt))),
          /* (2) */ hasParent(implicitCastExpr(hasParent(cStyleCastExpr(hasParent(capture_declstmt)))))
        ),
        to(varDecl(hasTypeLoc(typeLoc().bind("rvalue_type"))))
      ).bind("rvalue"),
      {
        change_declstmt,
        change_rvalue,
        add_include,
      },
      declaration_found("HandleRefExprVarDecl")
    );

  // <VarDecl <MemberExpr <DeclRefExpr>>>
  auto HandleRvalueMemberExprVarDecl = makeRule(
      expr(
        anyOf(
          /* (1) */ hasParent(implicitCastExpr(hasParent(capture_declstmt))),
          /* (2) */ hasParent(implicitCastExpr(hasParent(cStyleCastExpr(hasParent(capture_declstmt)))))
        ),
        capture_memberexpr_rvalue
      ),
      {
        change_declstmt,
        changeTo(
          node("rvalue"), 
          cat(
            "__trace_member_rvalue(", node("rvalue"), ", ", name("rvalue_type"), ", (", node("record_type"), "))"
          )
        ), 
        add_include,
      },
      assignment_found("HandleRvalueMemberExprVarDecl")
    );

  // TODO: <VarDecl <CallExpr>>
  // NOTE: 関数の戻り値をトラックすれば省略可能

  // <VarDecl <IntegerLiteral>>
/*
    |-DeclStmt 0x157d1b0 <line:52:5, col:14>
    | `-VarDecl 0x157d128 <col:5, col:13> col:9 used x 'int' cinit
    |   `-IntegerLiteral 0x157d190 <col:13> 'int' 3
*/
/* (a)
|   `-DeclStmt 0x1b815d8 <line:30:5, col:24>
|     `-VarDecl 0x1b81550 <col:5, col:23> col:16 init 'int' static cinit
|       `-IntegerLiteral 0x1b815b8 <col:23> 'int' 1
*/
  auto HandleIntegerLiteralVarDecl = makeRule(
      expr(integerLiteral(
        /* (a) */ hasParent(varDecl(unless(isStaticLocal()))),
        hasParent(capture_declstmt)
      )).bind("rvalue"),
      {
        change_declstmt,
        change_rvalue_const_int,
        add_include,
      },
      declaration_found("HandleIntegerLiteralVarDecl")
    );

  // <VarDecl <UnaryOperator <DeclRefExpr>>>
/*
|   |-DeclStmt 0xa306a0 <line:42:5, col:24>
|   | `-VarDecl 0xa30600 <col:5, col:23> col:18 used q 'struct pair *' cinit
|   |   `-UnaryOperator 0xa30688 <col:22, col:23> 'struct pair *' prefix '&' cannot overflow
|   |     `-DeclRefExpr 0xa30668 <col:23> 'struct pair':'struct pair' lvalue Var 0xa2f280 'p' 'struct pair':'struct pair'
*/
  auto HandleUnaryOperatorRefExprVarDecl = makeRule(
      unaryOperator(
        hasOperatorName("&"),
        hasParent(capture_declstmt),
        hasUnaryOperand(declRefExpr(
          to(varDecl(hasTypeLoc(typeLoc().bind("rvalue_type"))))
        ))
      ).bind("rvalue"),
      {
        change_declstmt,
        change_rvalue,
        add_include,
      },
      declaration_found("HandleUnaryOperatorRefExprVarDecl")
    );

  // <VarDecl <UnaryOperator <MemberExpr>>>
/*
|   |-DeclStmt 0x1c57578 <line:71:5, col:31>
|   | `-VarDecl 0x1c57460 <col:5, col:25> col:10 y 'int *' cinit
|   |   `-UnaryOperator 0x1c57560 <col:14, col:25> 'int *' prefix '&' cannot overflow
|   |     `-MemberExpr 0x1c57530 <col:15, col:25> 'int' lvalue .length 0x1c55f48
|   |       `-MemberExpr 0x1c57500 <col:15, col:18> 'struct (unnamed struct at bad.c:53:5)':'struct header::(unnamed at bad.c:53:5)' lvalue ->nested 0x1c561b8
|   |         `-ImplicitCastExpr 0x1c574e8 <col:15> 'struct header *' <LValueToRValue>
|   |           `-DeclRefExpr 0x1c574c8 <col:15> 'struct header *' lvalue Var 0x1c56c40 'h' 'struct header *'
*/
  auto HandleUnaryOperatorMemberExprVarDecl = makeRule(
      unaryOperator(
        hasOperatorName("&"),
        hasParent(capture_declstmt),
        hasUnaryOperand(capture_memberexpr_rvalue)
      ).bind("rvalue"),
      {
        change_declstmt,
        changeTo(
          node("rvalue"), 
          cat(
            "__trace_member_rvalue(", node("rvalue"), ", (", name("rvalue_type"), "), (", node("record_type"), "))"
          )
        ), 
        add_include,
      },
      assignment_found("HandleUnaryOperatorMemberExprVarDecl")
    );

  // <VarDecl <ArraySubscriptExpr>>
/*
|   |-DeclStmt 0x1650218 <line:83:5, col:30>
|   | `-VarDecl 0x1650120 <col:5, col:29> col:18 x 'unsigned int' cinit
|   |   `-ImplicitCastExpr 0x1650200 <col:22, col:29> 'unsigned int' <LValueToRValue>
|   |     `-ArraySubscriptExpr 0x16501e0 <col:22, col:29> 'unsigned int' lvalue
|   |       |-ImplicitCastExpr 0x16501c8 <col:22> 'unsigned int *' <ArrayToPointerDecay>
|   |       | `-DeclRefExpr 0x1650188 <col:22> 'unsigned int[3]' lvalue Var 0x164fea0 'array' 'unsigned int[3]'
|   |       `-IntegerLiteral 0x16501a8 <col:28> 'int' 1
*/
  auto HandleArraySubscriptExprVarDecl = makeRule(
      arraySubscriptExpr(
        hasParent(implicitCastExpr(hasParent(capture_declstmt))),
        hasBase(__capture_record_type), 
        hasType(qualType().bind("rvalue_type"))
      ).bind("rvalue"),
      {
        change_declstmt,
        changeTo(
          node("rvalue"), 
          cat(
            "__trace_member_rvalue(", node("rvalue"), ", ", "FIXME", ", (", node("record_type"), "))"
          )
        ),
        add_include,
      },
      declaration_found("HandleArraySubscriptExprVarDecl")
    );

  // <VarDecl <UnaryOperator <ArraySubscriptExpr>>>
/*
|   `-DeclStmt 0x1c57fe0 <line:82:5, col:23>
|     `-VarDecl 0x1c57ee8 <col:5, col:22> col:10 y 'int *' cinit
|       `-UnaryOperator 0x1c57fc8 <col:14, col:22> 'int *' prefix '&' cannot overflow
|         `-ArraySubscriptExpr 0x1c57fa8 <col:15, col:22> 'int' lvalue
|           |-ImplicitCastExpr 0x1c57f90 <col:15> 'int *' <ArrayToPointerDecay>
|           | `-DeclRefExpr 0x1c57f50 <col:15> 'int[3]' lvalue Var 0x1c57ba0 'array' 'int[3]'
|           `-IntegerLiteral 0x1c57f70 <col:21> 'int' 0
*/
  auto HandleUnaryOperatorArraySubscriptExprVarDecl = makeRule(
      unaryOperator(
        hasOperatorName("&"),
        hasParent(capture_declstmt),
        hasUnaryOperand(arraySubscriptExpr(
          hasBase(__capture_record_type), 
          hasType(qualType().bind("rvalue_type"))
        ))
      ).bind("rvalue"),
      {
        change_declstmt,
        changeTo(
          node("rvalue"), 
          cat(
            "__trace_member_rvalue(", node("rvalue"), ", ", "FIXME", ", (", node("record_type"), "))"
          )
        ),
        add_include,
      },
      declaration_found("HandleUnaryOperatorArraySubscriptExprVarDecl")
    );

  // <VarDecl <CallExpr>>
/*
|   |-DeclStmt 0xa18ee0 <line:34:5, col:17>
|   | `-VarDecl 0xa18df8 <col:5, col:16> col:9 used x 'int' cinit
|   |   `-CallExpr 0xa18eb8 <col:13, col:16> 'int'
|   |     |-ImplicitCastExpr 0xa18ea0 <col:13> 'int (*)(int)' <FunctionToPointerDecay>
|   |     | `-DeclRefExpr 0xa18e60 <col:13> 'int (int)' Function 0xa176e0 'f' 'int (int)'
|   |     `-IntegerLiteral 0xa18e80 <col:15> 'int' 1
*/
  auto HandleVarDecl = makeRule(
      capture_declstmt,
      {
        change_declstmt,
        add_include,
      },
      declaration_found("HandleVarDecl")
    );

  // <AssignOperator <DeclRefExpr> <???>>
  // lvalue をハンドルするのみ
  // FIXME: マクロの場合は無視
  auto HandleLvalueDeclRefExprAssignment = makeRule(
      expr(
        unless(isInMacro()),
        hasParent(binaryOperator(
          hasLHS(declRefExpr()),
          isAssignmentOperator()
        )),
        capture_declrefexpr_lvalue
      ),
      {
        change_lvalue,
        add_include,
      },
      assignment_found("HandleLvalueDeclRefExprAssignment")
    );

  // <MemberExpr> = <???>
  // lvalue をハンドルするのみ
  auto HandleLvalueMemberExprAssignment = makeRule(
      expr(
        hasParent(binaryOperator(
          hasLHS(memberExpr()),
          isAssignmentOperator()
        )),
        capture_memberexpr_lvalue
      ),
      change_member_lvalue,
      assignment_found("HandleLvalueMemberExprAssignment")
    );

  // 配列への代入
  // lvalueのみ扱う
/*
|   |-BinaryOperator 0x1003068 <line:82:5, col:16> 'int' '='
|   | |-ArraySubscriptExpr 0x1003028 <col:5, col:12> 'int' lvalue
|   | | |-ImplicitCastExpr 0x1003010 <col:5> 'int *' <ArrayToPointerDecay>
|   | | | `-DeclRefExpr 0x1002fd0 <col:5> 'int[3]' lvalue Var 0x1002e80 'array' 'int[3]'
|   | | `-IntegerLiteral 0x1002ff0 <col:11> 'int' 0
|   | `-IntegerLiteral 0x1003048 <col:16> 'int' 1
*/
  auto HandleLvalueArraySubscriptExprAssignment = makeRule(
      expr(
        hasParent(binaryOperator(isAssignmentOperator())),
        arraySubscriptExpr(
          hasBase(__capture_record_type),
          hasType(qualType().bind("lvalue_type"))
        )
      ).bind("lvalue"),
      {
        // change_member_lvalue,
        changeTo(
          node("lvalue"), 
          cat(
            "__trace_member_lvalue(", node("lvalue"), ", ", "FIXME", ", (", node("record_type"), "))"
          )
        ),
        add_include,
      },
      assignment_found("HandleLvalueArraySubscriptExprAssignment")
    );

  // <???> = <DeclRefExpr>;
  // rvalue をハンドルするのみ
  auto HandleRvalueDeclRefExprAssignment = makeRule(
      // TODO: v += u を v = v + u に正規化
      expr(
        unless(isInMacro()),
        hasParent(binaryOperator(
          hasRHS(ignoringImpCasts(declRefExpr())),
          isAssignmentOperator()
        )),
        capture_declrefexpr_rvalue
      ),
      {
        change_rvalue,
        add_include,
      },
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
/*
|   |-BinaryOperator 0x1381a28 <line:27:5, col:9> 'unsigned int' '='
|   | |-DeclRefExpr 0x13819d0 <col:5> 'unsigned int' lvalue Var 0x1381820 'z' 'unsigned int'
|   | `-ImplicitCastExpr 0x1381a10 <col:9> 'unsigned int' <IntegralCast>
|   |   `-IntegerLiteral 0x13819f0 <col:9> 'int' 0
*/
  auto HandleRvalueLiteralAssignment = makeRule(
      // TODO: v += u を v = v + u に正規化
      expr(
        integerLiteral(anyOf(
          hasParent(capture_assign_operator),
          hasParent(implicitCastExpr(hasParent(capture_assign_operator)))
        ))
      ).bind("rvalue"),
      {
        change_rvalue_const_int,
        add_include,
      },
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
      {
        changeTo(
          node("expr"),
          cat(
            "(__trace_variable_lvalue(", node("lvalue"), ", (", node("lvalue_type"), "))"
            " += ",
            "__trace_variable_rvalue(1, const int))"
          )
        ),
        add_include,
      },
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
      {
        changeTo(
          node("rvalue"), 
          cat(
            "__trace_member_rvalue(", node("rvalue"), ", (", name("rvalue_type"), "), (", node("record_type"), "))"
          )
        ),
        add_include,
      },
      assignment_found("HandleRvalueMemberExprAssignment")
    );

/*
|   `-SwitchStmt 0x7a1a78 <line:106:5, line:109:5>
|     |-ImplicitCastExpr 0x7a1a60 <line:106:13> 'int' <LValueToRValue>
|     | `-DeclRefExpr 0x7a1a40 <col:13> 'int' lvalue Var 0x7a19a0 'x' 'int'
|     `-CompoundStmt 0x7a1b48 <col:16, line:109:5>
|       `-CaseStmt 0x7a1b18 <line:107:9, line:108:13>
|         |-ConstantExpr 0x7a1b00 <line:107:14, col:18> 'int'
|         | `-BinaryOperator 0x7a1ae0 <col:14, col:18> 'int' '+'
|         |   |-IntegerLiteral 0x7a1aa0 <col:14> 'int' 1
|         |   `-IntegerLiteral 0x7a1ac0 <col:18> 'int' 3
|         `-BreakStmt 0x7a1b40 <line:108:13>
*/
  auto is_not_in_case = unless(hasAncestor(caseStmt()));
  auto is_not_in_initlistexpr = unless(hasAncestor(initListExpr()));
  auto is_not_in_vardecl = unless(hasAncestor(varDecl())); // e.g. int array[1+2]
  auto is_binary_operator = hasAncestor(binaryOperator(unless(isAssignmentOperator())));

  // <BinaryOperator <DeclRefExpr> ...>
  // rvalue のみchangeTo
  auto HandleRvalueDeclRefExprBinaryOperator = makeRule(
      declRefExpr(
        is_not_in_case,
        unless(isInMacro()),
        is_binary_operator,
        to(varDecl(hasTypeLoc(typeLoc().bind("rvalue_type"))))
      ).bind("rvalue"),
      {
        change_rvalue,
        add_include,
      },
      assignment_found("HandleRvalueDeclRefExprBinaryOperator")
    );

  // <BinaryOperator <MemberExpr> ...>
  // rvalue をハンドルするのみ
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
        is_not_in_case,
        is_binary_operator,
        capture_memberexpr_rvalue
      ),
      {
        change_rvalue,
        add_include,
      },
      assignment_found("HandleRvalueMemberExprBinaryOperator")
    );

  // <BinaryOperator <IntegerLiteral> ...>
  auto HandleIntegerLiteralBinaryOperator = makeRule(
      expr(integerLiteral(
        unless(hasAncestor(fieldDecl())), // e.g. struct { int array[16 + 0]; }
        is_not_in_case,
        is_not_in_initlistexpr,
        is_not_in_vardecl, // FIXME: int y = f(2) + 3; がスルーされる
        is_binary_operator
      )).bind("rvalue"),
      {
        change_rvalue_const_int,
        add_include,
      },
      assignment_found("HandleIntegerLiteralBinaryOperator")
    );

  // TODO: <BinaryOperator <ArraySubscriptExpr> ...>
/*
|   `-DeclStmt 0x21b9618 <line:86:5, col:32>
|     `-VarDecl 0x21b9440 <col:5, col:31> col:9 z 'int' cinit
|       `-ImplicitCastExpr 0x21b9600 <col:13, col:31> 'int' <IntegralCast>
|         `-BinaryOperator 0x21b95e0 <col:13, col:31> 'unsigned int' '+'
|           |-ImplicitCastExpr 0x21b95b0 <col:13, col:20> 'unsigned int' <LValueToRValue>
|           | `-ArraySubscriptExpr 0x21b9500 <col:13, col:20> 'unsigned int' lvalue
|           |   |-ImplicitCastExpr 0x21b94e8 <col:13> 'unsigned int *' <ArrayToPointerDecay>
|           |   | `-DeclRefExpr 0x21b94a8 <col:13> 'unsigned int[3]' lvalue Var 0x21b8f70 'array' 'unsigned int[3]'
|           |   `-IntegerLiteral 0x21b94c8 <col:19> 'int' 0
|           `-ImplicitCastExpr 0x21b95c8 <col:24, col:31> 'unsigned int' <LValueToRValue>
|             `-ArraySubscriptExpr 0x21b9590 <col:24, col:31> 'unsigned int' lvalue
|               |-ImplicitCastExpr 0x21b9560 <col:24> 'unsigned int *' <ArrayToPointerDecay>
|               | `-DeclRefExpr 0x21b9520 <col:24> 'unsigned int[3]' lvalue Var 0x21b8f70 'array' 'unsigned int[3]'
|               `-ImplicitCastExpr 0x21b9578 <col:30> 'unsigned int' <LValueToRValue>
|                 `-DeclRefExpr 0x21b9540 <col:30> 'unsigned int' lvalue Var 0x21b91f0 'x' 'unsigned int'
*/


  // TODO: 関数呼び出しありの代入

  // <BinaryOperator <DeclRefExpr> ...>
  auto HandleCompareOperator = makeRule(
      binaryOperator(anyOf(
        isComparisonOperator(),
        hasAnyOperatorName("||", "&&")
      )).bind("expr"),
      {
        changeTo(
          node("expr"), 
          cat(
            "__trace_condition(", node("expr"), ")"
          )
        ),
        add_include,
      },
      compare_found
    );

  // <ReturnStmt <DeclRefExpr>>
  auto HandleDeclRefExprReturnStmt = makeRule(
      returnStmt(hasReturnValue(ignoringImpCasts(declRefExpr(
        to(varDecl(hasTypeLoc(typeLoc().bind("rvalue_type"))))
      ).bind("rvalue")))),
      {
        change_rvalue,
        add_include,
      },
      return_found("HandleDeclRefExprReturnStmt")
    );

  // <ReturnStmt <IntegerLiteral>>
  auto HandleIntegerLiteralReturnStmt = makeRule(
      returnStmt(hasReturnValue(expr(integerLiteral()).bind("rvalue"))),
      {
        change_rvalue_const_int,
        add_include,
      },
      return_found("HandleIntegerLiteralReturnStmt")
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

  // <ReturnStmt>
  auto HandleReturnStmt = makeRule(
      returnStmt(hasReturnValue(expr().bind("ReturnValue"))),
      {
        changeTo(before(node("ReturnValue")), cat("__trace_function_return(")),
        changeTo(after(node("ReturnValue")), cat(")")),
        add_include,
      },
      return_found("HandleReturnStmt")
    );

  // TODO: 関数呼び出しの呼び出し元と呼び出し先の値のマッチング
  // <CallExpr>
/*
|       `-CallExpr 0x152d610 <col:13, col:21> 'int'
|         |-ImplicitCastExpr 0x152d5f8 <col:13> 'int (*)(int, int)' <FunctionToPointerDecay>
|         | `-DeclRefExpr 0x152d568 <col:13> 'int (int, int)' Function 0x152b9c0 'add' 'int (int, int)'
|         |-IntegerLiteral 0x152d588 <col:17> 'int' 1
|         `-ImplicitCastExpr 0x152d640 <col:20> 'int' <LValueToRValue>
|           `-DeclRefExpr 0x152d5a8 <col:20> 'int' lvalue Var 0x152d430 'y' 'int'
*/
  auto HandleCallExpr = makeRule(
      callExpr(forEachArgumentWithParam(
        expr().bind("Argument"),
        parmVarDecl().bind("Param")
      )),
      {
        changeTo(before(node("Argument")), cat("__trace_function_call_param(")),
        changeTo(after(node("Argument")), cat(", ", name("Param"), ")")),
        add_include,
      },
      cat("HandleCallExpr")
    );

  return applyFirst({
    HandleTraceFunctionCall, // 無意味

    HandleCallExpr,
    
    HandleRefExprVarDecl,
    HandleRvalueMemberExprVarDecl,
    HandleIntegerLiteralVarDecl,
    HandleUnaryOperatorRefExprVarDecl,
    HandleUnaryOperatorMemberExprVarDecl,
    HandleArraySubscriptExprVarDecl,
    HandleUnaryOperatorArraySubscriptExprVarDecl,
    HandleVarDecl,
    
    HandleLvalueDeclRefExprAssignment,
    HandleLvalueMemberExprAssignment,
    HandleLvalueArraySubscriptExprAssignment,
    HandleRvalueDeclRefExprAssignment,
    HandleRvalueLiteralAssignment,
    HandleRvalueMemberExprAssignment,

    HandleRvalueLiteralUnaryOperator,
    HandleRvalueDeclRefExprBinaryOperator,
    HandleRvalueMemberExprBinaryOperator,
    HandleIntegerLiteralBinaryOperator,
    HandleCompareOperator,

    HandleDeclRefExprReturnStmt,
    HandleIntegerLiteralReturnStmt,
    HandleReturnStmt,
  });
}

VariableUpdateTracingCheck::VariableUpdateTracingCheck(StringRef Name,
                                               ClangTidyContext *Context)
    : utils::TransformerClangTidyCheck(VariableUpdateTracingCheckImpl(), Name, Context) {}

} // namespace misc
} // namespace tidy
} // namespace clang
