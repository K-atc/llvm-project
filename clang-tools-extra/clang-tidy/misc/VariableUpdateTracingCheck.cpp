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
  auto assignment_found = cat("assignment found 🎉");

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

  // <DeclStmt>
  // 初期化パターンを網羅するのが難しい。特に構造体
  // auto HandleDeclStmt = makeRule(
  //   declStmt(hasSingleDecl(varDecl(
  //     hasTypeLoc(typeLoc().bind("lvalue_type"))
  //   ).bind("lvalue"))),
  //   {
  //     changeTo(
  //       after(node("lvalue")),
  //       cat(
  //         " __trace_variable_declaration(", name("lvalue"), ", ", name("lvalue_type"), ");"
  //       )
  //     ),
  //   },
  //   declaration_found
  // );

/*
|   |-DeclStmt 0x14a25f8 <line:29:5, col:14>
|   | `-VarDecl 0x14a2558 <col:5, col:13> col:9 used z 'int' cinit
|   |   `-ImplicitCastExpr 0x14a25e0 <col:13> 'int' <LValueToRValue>
|   |     `-DeclRefExpr 0x14a25c0 <col:13> 'int' lvalue Var 0x14a2308 'x' 'int'
*/
  // <DeclStmt <VarDecl> = <DeclRefExpr>>
  auto HandleDeclRefExprDeclStmt = makeRule(
      declRefExpr(
        hasParent(implicitCastExpr(
          hasParent(varDecl())
        )),
        to(varDecl(hasTypeLoc(typeLoc().bind("var_type"))))
      ).bind("var"),
      changeTo(
        node("var"), 
        cat(
          "__trace_variable_rvalue(", name("var"), ", ", name("var_type"), ")"
        )
      ),
      declaration_found
    );

  auto capture_declrefexpr_lvalue = hasLHS(
      declRefExpr(
        to(varDecl(hasTypeLoc(typeLoc().bind("lvalue_type"))))
      ).bind("lvalue")
    );
  auto capture_memberexpr_lvalue = hasLHS(
      memberExpr(member(
        fieldDecl(hasTypeLoc(typeLoc().bind("lvalue_type")))
      )).bind("lvalue")
    );
  auto change_lvalue = changeTo(
      node("lvalue"), 
      cat(
        "__trace_variable_lvalue(", name("lvalue"), ", ", name("lvalue_type"), ")"
      )
    );

  // <DeclRefExpr> = <DeclRefExpr>;
  auto HandleRvalueDeclRefExprAssignment = makeRule(
      // TODO: v += u を v = v + u に正規化
      binaryOperator(
        isAssignmentOperator(),
        capture_declrefexpr_lvalue,
        hasRHS(ignoringImpCasts(
          declRefExpr(anyOf(
            // 一時変数
            to(varDecl(hasTypeLoc(typeLoc().bind("rvalue_type")))),
            // 関数引数
            to(parmVarDecl(hasTypeLoc(typeLoc().bind("rvalue_type"))))
          )).bind("rvalue")
        ))
      ),
      {
        change_lvalue,
        changeTo(
          node("rvalue"), 
          cat(
            "__trace_variable_rvalue(", name("rvalue"), ", ", name("rvalue_type"), ")"
          )
        ), 
      },
      assignment_found
    );

  // <DeclRefExpr> = <IntegerLiteral>
  auto HandleRvalueLiteralAssignment = makeRule(
      // TODO: v += u を v = v + u に正規化
      binaryOperator(
        isAssignmentOperator(),
        capture_declrefexpr_lvalue,
        hasRHS(
          expr(integerLiteral()).bind("rvalue")
        )
      ),
      {
        change_lvalue,
        changeTo(
          node("rvalue"), 
          cat(
            "__trace_variable_rvalue(", node("rvalue"), ", ", "const int", ")"
          )
        ), 
      },
      assignment_found
    );

  // TODO: 構造体メンバー = <DeclRefExpr>
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
        hasRHS(ignoringImpCasts(
          declRefExpr(anyOf(
            // 一時変数
            to(varDecl(hasTypeLoc(typeLoc().bind("rvalue_type")))),
            // 関数引数
            to(parmVarDecl(hasTypeLoc(typeLoc().bind("rvalue_type"))))
          )).bind("rvalue")
        ))
      ),
      {
        changeTo(
          node("lvalue"), 
          cat(
            "__trace_variable_lvalue(", node("lvalue"), ", ", name("lvalue_type"), ")"
          )
        ),
        changeTo(
          node("rvalue"), 
          cat(
            "__trace_variable_rvalue(", name("rvalue"), ", ", name("rvalue_type"), ")"
          )
        ), 
      },
      assignment_found
    );

  // <BinaryOperator <DeclRefExpr> ...>
  auto HandleRvalueBinaryOperatorDeclRefExprBinaryOperator = makeRule(
      declRefExpr(
        hasParent(implicitCastExpr(
          hasParent(binaryOperator(unless(isAssignmentOperator())))
        )),
        to(varDecl(hasTypeLoc(typeLoc().bind("var_type"))))
      ).bind("var"),
      changeTo(
        node("var"), 
        cat(
          "__trace_variable_rvalue(", name("var"), ", ", name("var_type"), ")"
        )
      ),
      assignment_found
    );

  // <BinaryOperator <IntegerLiteral> ...>
  auto HandleRvalueBinaryOperatorIntegerLiteralBinaryOperator = makeRule(
      expr(integerLiteral(
        hasParent(binaryOperator(unless(isAssignmentOperator())))
      )).bind("var"),
      changeTo(
        node("var"), 
        cat(
          "__trace_variable_rvalue(", node("var"), ", ", "const int", ")"
        )
      ),
      assignment_found
    );

  // TODO: 関数呼び出しありの代入

  // <ReturnStmt <DeclRefExpr>>
  auto HandleDeclRefExprReturnStmt = makeRule(
      returnStmt(hasReturnValue(ignoringImpCasts(declRefExpr(
        to(varDecl(hasTypeLoc(typeLoc().bind("var_type"))))
      ).bind("var")))),
      changeTo(
        node("var"), 
        cat(
          "__trace_variable_rvalue(", node("var"), ", ", name("var_type"), ")"
        )
      ),
      cat("Function return statement found 📢")
    );

  // <ReturnStmt <IntegerLiteral>>
  auto HandleIntegerLiteralReturnStmt = makeRule(
      returnStmt(hasReturnValue(expr(integerLiteral()).bind("var"))),
      changeTo(
        node("var"), 
        cat(
          "__trace_variable_rvalue(", node("var"), ", ", "const int", ")"
        )
      ),
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
    // HandleDeclStmt,
    HandleDeclRefExprDeclStmt,
    HandleRvalueDeclRefExprAssignment,
    HandleRvalueLiteralAssignment,
    HandleLvalueMemberExprRvalueDeclRefExprAssignment,
    HandleRvalueBinaryOperatorDeclRefExprBinaryOperator,
    HandleRvalueBinaryOperatorIntegerLiteralBinaryOperator,
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
