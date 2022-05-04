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
  
  // TODO: 変数宣言 int lhs = 1;
  
  // lhs = <value>;
  auto HandleAssignment = makeRule(
      binaryOperator(
        hasOperatorName("="), 
        hasLHS(
          declRefExpr(
            to(varDecl(hasTypeLoc(typeLoc().bind("lhs_type"))))
          ).bind("lhs")
        )
        // TODO: RHSの型
      ),
      changeTo(
        node("lhs"), 
        cat("__trace_variable_update(", name("lhs"), ", ", name("lhs_type"), ")")
      ), 
      assignment_found
    );

  // TODO: 関数呼び出しありの代入・変数宣言

  return applyFirst({
    // HandleX,
    // HandleY,
    HandleAssignment,
  });
}

VariableUpdateTracingCheck::VariableUpdateTracingCheck(StringRef Name,
                                               ClangTidyContext *Context)
    : utils::TransformerClangTidyCheck(VariableUpdateTracingCheckImpl(), Name, Context) {}

} // namespace misc
} // namespace tidy
} // namespace clang
