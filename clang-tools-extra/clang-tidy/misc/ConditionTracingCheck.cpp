//===--- ConditionTracingCheck.cpp - clang-tidy ---------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "ConditionTracingCheck.h"
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

using namespace clang::ast_matchers;

namespace clang {
namespace ast_matchers {

AST_MATCHER(Stmt, isInMacro) {
  return Node.getBeginLoc().isMacroID();
}

} // namespace clang
} // namespace ast_matchers

namespace clang {
namespace tidy {
namespace misc {

using namespace ::clang::ast_matchers;
using namespace ::clang::transformer;

RewriteRuleWith<std::string> ConditionTracingCheckImpl() {
  std::cerr << "[*] ConditionTracingCheckImpl" << std::endl;

  auto add_include = addInclude("trace.h", IncludeFormat::Angled);

  auto condition_found = [](auto rule_name) { return cat("Compare found 🏆 (", rule_name, ")"); };

  auto trace_condition_change_set = {
      insertBefore(node("expr"), cat("__trace_condition((")),
      insertAfter(node("expr"), cat("))")),
      add_include,
    };

  // auto HandleBinaryOperatorIfStmtCondition = makeRule(
  //     binaryOperator(
  //       // unless(hasAncestor(binaryOperator())), // 最長一致
  //       // anyOf(
  //       //   isComparisonOperator(),
  //       //   hasAnyOperatorName("||", "&&")
  //       // )
  //       hasParent(ifStmt())
  //     ).bind("expr"),
  //     trace_condition_change_set,
  //     condition_found("HandleBinaryOperatorIfStmtCondition")
  //   );

  auto HandleIfStmtCondition = makeRule(
      ifStmt(
        hasCondition(expr(unless(isInMacro())).bind("expr"))
      ),
      trace_condition_change_set,
      condition_found("HandleIfStmtCondition")
    );

  auto HandleWhileStmtCondition = makeRule(
      whileStmt(
        hasCondition(expr(unless(isInMacro())).bind("expr"))
      ),
      trace_condition_change_set,
      condition_found("HandleWhileStmtCondition")
    );

  auto HandleForStmtCondition = makeRule(
      forStmt(
        hasCondition(expr(unless(isInMacro())).bind("expr"))
      ),
      trace_condition_change_set,
      condition_found("HandleForStmtCondition")
    );

  return applyFirst({
    HandleIfStmtCondition,
    // HandleBinaryOperatorIfStmtCondition,
    HandleWhileStmtCondition,
    HandleForStmtCondition,
  });
}

ConditionTracingCheck::ConditionTracingCheck(StringRef Name,
                                               ClangTidyContext *Context)
    : utils::TransformerClangTidyCheck(ConditionTracingCheckImpl(), Name, Context) {}


} // namespace misc
} // namespace tidy
} // namespace clang
