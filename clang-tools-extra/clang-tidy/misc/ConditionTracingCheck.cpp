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


using namespace clang::ast_matchers;

namespace clang {
namespace tidy {
namespace misc {

using namespace ::clang::ast_matchers;
using namespace ::clang::transformer;

RewriteRuleWith<std::string> ConditionTracingCheckImpl() {
  auto add_include = addInclude("trace.h", IncludeFormat::Angled);

  auto condition_found = [](auto rule_name) { return cat("Compare found 🏆 (", rule_name, ")"); };

  auto trace_condition_change_set = {
      insertBefore(node("expr"), cat("__trace_condition((")),
      insertAfter(node("expr"), cat("))")),
      add_include,
    };

  auto HandleBinaryOperatorCondition = makeRule(
      binaryOperator(
        unless(hasAncestor(varDecl())),
        unless(hasAncestor(returnStmt())),
        unless(hasAncestor(binaryOperator())), // 最長一致
        anyOf(
          isComparisonOperator(),
          hasAnyOperatorName("||", "&&")
        )
      ).bind("expr"),
      trace_condition_change_set,
      condition_found("HandleBinaryOperatorCondition")
    );

  auto HandleWhileStmtCondition = makeRule(
      whileStmt(hasCondition(expr().bind("expr"))),
      trace_condition_change_set,
      condition_found("HandleWhileStmtCondition")
    );

  auto HandleForStmtCondition = makeRule(
      forStmt(hasCondition(expr().bind("expr"))),
      trace_condition_change_set,
      condition_found("HandleForStmtCondition")
    );

  return applyFirst({
    HandleWhileStmtCondition,
    HandleForStmtCondition,
    HandleBinaryOperatorCondition,
  });
}

ConditionTracingCheck::ConditionTracingCheck(StringRef Name,
                                               ClangTidyContext *Context)
    : utils::TransformerClangTidyCheck(ConditionTracingCheckImpl(), Name, Context) {}


} // namespace misc
} // namespace tidy
} // namespace clang
