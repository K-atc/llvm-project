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

  auto assignment_found =
      cat("assignment found 🎉");

  // auto HandleX = makeRule(
  //     functionDecl(hasName("bad")).bind("name"),
  //     changeTo(name("name"), cat("good")),
  //     cat("bad is now good")
  //   );

  // auto HandleY = makeRule(declRefExpr(to(functionDecl(hasName("MkX")))),
  //        changeTo(cat("MakeX")),
  //        cat("MkX has been renamed MakeX"));
  
  // TODO: 初期化ありの変数宣言 int lhs = 1;

  auto capture_lvalue = hasLHS(
      declRefExpr(
        to(varDecl(hasTypeLoc(typeLoc().bind("lvalue_type"))))
      ).bind("lvalue")
    );
  auto change_lvalue = changeTo(
      node("lvalue"), 
      cat(
        "__trace_variable_update_lvalue(", name("lvalue"), ", ", name("lvalue_type"), ")"
      )
    );
  
  // <DeclRefExpr> = <DeclRefExpr>;
  auto HandleRvalueDeclRefExprAssignment = makeRule(
      // TODO: v += u を v = v + u に正規化
      binaryOperator(
        isAssignmentOperator(),
        capture_lvalue,
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
            "__trace_variable_update_rvalue(", name("rvalue"), ", ", name("rvalue_type"), ")"
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
        capture_lvalue,
        hasRHS(
          expr(integerLiteral()).bind("rvalue")
        )
      ),
      {
        change_lvalue,
        changeTo(
          node("rvalue"), 
          cat(
            "__trace_variable_update_rvalue(", node("rvalue"), ", ", "const int", ")"
          )
        ), 
      },
      assignment_found
    );

  // <DeclRefExpr> = ... <DeclRefExpr> ...
  auto HandleRvalueBinaryOperatorDeclRefExprAssignment = makeRule(
      declRefExpr(
        hasParent(implicitCastExpr(
          hasParent(binaryOperator(unless(isAssignmentOperator())))
        )),
        to(varDecl(hasTypeLoc(typeLoc().bind("var_type"))))
      ).bind("var"),
      changeTo(
        node("var"), 
        cat(
          "__trace_variable_update_rvalue(", name("var"), ", ", name("var_type"), ")"
        )
      ),
      assignment_found
    );

  // <DeclRefExpr> = ... <IntegerLiteral> ...
  auto HandleRvalueBinaryOperatorIntegerLiteralAssignment = makeRule(
      expr(integerLiteral(
        hasParent(binaryOperator(unless(isAssignmentOperator())))
      )).bind("var"),
      changeTo(
        node("var"), 
        cat(
          "__trace_variable_update_rvalue(", node("var"), ", ", "const int", ")"
        )
      ),
      assignment_found
    );

  // TODO: 関数呼び出しありの代入

  return applyFirst({
    HandleRvalueDeclRefExprAssignment,
    HandleRvalueLiteralAssignment,
    HandleRvalueBinaryOperatorDeclRefExprAssignment,
    HandleRvalueBinaryOperatorIntegerLiteralAssignment,
  });
}

VariableUpdateTracingCheck::VariableUpdateTracingCheck(StringRef Name,
                                               ClangTidyContext *Context)
    : utils::TransformerClangTidyCheck(VariableUpdateTracingCheckImpl(), Name, Context) {}

} // namespace misc
} // namespace tidy
} // namespace clang
