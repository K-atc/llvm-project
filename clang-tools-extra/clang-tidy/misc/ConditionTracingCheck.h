//===--- ConditionTracingCheck.h - clang-tidy -------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_TOOLS_EXTRA_CLANG_TIDY_MISC_CONDITIONTRACINGCHECK_H
#define LLVM_CLANG_TOOLS_EXTRA_CLANG_TIDY_MISC_CONDITIONTRACINGCHECK_H

#include "../utils/TransformerClangTidyCheck.h"

namespace clang {
namespace tidy {
namespace misc {

class ConditionTracingCheck : public utils::TransformerClangTidyCheck {
public:
  ConditionTracingCheck(StringRef Name, ClangTidyContext *Context);

  bool isLanguageVersionSupported(const LangOptions &LangOpts) const override {
    // return LangOpts.CPlusPlus;
    return true;
  }
};

} // namespace misc
} // namespace tidy
} // namespace clang

#endif // LLVM_CLANG_TOOLS_EXTRA_CLANG_TIDY_MISC_CONDITIONTRACINGCHECK_H
