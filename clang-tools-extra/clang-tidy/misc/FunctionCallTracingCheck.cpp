//===--- FunctionCallTracingCheck.cpp - clang-tidy ------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "FunctionCallTracingCheck.h"
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
namespace ast_matchers {

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

RewriteRuleWith<std::string> FunctionCallTracingCheckImpl() {
  auto add_include = addInclude("trace.h", IncludeFormat::Angled);

  auto function_found = [](auto rule_name) { return cat("Function declaration found 🎈 (", rule_name, ")"); };
  auto return_found = [](auto rule_name) { return cat("Return statement found 📢 (", rule_name, ")"); };

/*
|-FunctionDecl 0x20dc9e0 <line:7:1, line:9:1> line:7:5 used add 'int (int, int)'
| |-ParmVarDecl 0x20dc880 <col:9, col:13> col:13 used x 'int'
| |-ParmVarDecl 0x20dc900 <col:16, col:20> col:20 used y 'int'
| `-CompoundStmt 0x20dcb30 <col:23, line:9:1>
|   `-ReturnStmt 0x20dcb20 <line:8:5, col:16>
*/
  auto capture_body = hasBody(compoundStmt().bind("body"));
  auto capture_paramvardecl = [](unsigned N) { 
      return hasParameter(
        N,
        parmVarDecl(
          hasTypeLoc(typeLoc().bind("param_type" + std::to_string(N)))
        ).bind("param" + std::to_string(N))
      );
    };
  auto change_paramvardecl = [](unsigned N) { 
      return insertBefore(
        node("body"),
        cat(
          "__trace_function_param_decl(",
          name("param" + std::to_string(N)),
          ", (",
          name("param_type" + std::to_string(N)),
          ")); "
        )
      );
    };
  auto change_paramvardecl_begin = insertBefore(node("body"), cat("{ __trace_function_call_enter(); "));
  auto change_paramvardecl_terminal = insertAfter(node("body"), cat(" }"));
  auto HandleFunctionDecl1 = makeRule(
      functionDecl(
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        capture_paramvardecl(0),
        capture_body
      ),
      {
        change_paramvardecl_begin,
        change_paramvardecl(0),
        change_paramvardecl_terminal,
        add_include,
      },
      function_found("HandleFunctionDecl1")
    );
  auto HandleFunctionDecl2 = makeRule(
      functionDecl(
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        capture_paramvardecl(0),
        capture_paramvardecl(1),
        capture_body
      ),
      {
        change_paramvardecl_begin,
        change_paramvardecl(0),
        change_paramvardecl(1),
        change_paramvardecl_terminal,
        add_include,
      },
      function_found("HandleFunctionDecl2")
    );
  auto HandleFunctionDecl3 = makeRule(
      functionDecl(
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        capture_paramvardecl(0),
        capture_paramvardecl(1),
        capture_paramvardecl(2),
        capture_body
      ),
      {
        change_paramvardecl_begin,
        change_paramvardecl(0),
        change_paramvardecl(1),
        change_paramvardecl(2),
        change_paramvardecl_terminal,
        add_include,
      },
      function_found("HandleFunctionDecl3")
    );
  auto HandleFunctionDecl4 = makeRule(
      functionDecl(
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        capture_paramvardecl(0),
        capture_paramvardecl(1),
        capture_paramvardecl(2),
        capture_paramvardecl(3),
        capture_body
      ),
      {
        change_paramvardecl_begin,
        change_paramvardecl(0),
        change_paramvardecl(1),
        change_paramvardecl(2),
        change_paramvardecl(3),
        change_paramvardecl_terminal,
        add_include,
      },
      function_found("HandleFunctionDecl4")
    );
  auto HandleFunctionDecl5 = makeRule(
      functionDecl(
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        capture_paramvardecl(0),
        capture_paramvardecl(1),
        capture_paramvardecl(2),
        capture_paramvardecl(3),
        capture_paramvardecl(4),
        capture_body
      ),
      {
        change_paramvardecl_begin,
        change_paramvardecl(0),
        change_paramvardecl(1),
        change_paramvardecl(2),
        change_paramvardecl(3),
        change_paramvardecl(4),
        change_paramvardecl_terminal,
        add_include,
      },
      function_found("HandleFunctionDecl5")
    );
  auto HandleFunctionDecl6 = makeRule(
      functionDecl(
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        capture_paramvardecl(0),
        capture_paramvardecl(1),
        capture_paramvardecl(2),
        capture_paramvardecl(3),
        capture_paramvardecl(4),
        capture_paramvardecl(5),
        capture_body
      ),
      {
        change_paramvardecl_begin,
        change_paramvardecl(0),
        change_paramvardecl(1),
        change_paramvardecl(2),
        change_paramvardecl(3),
        change_paramvardecl(4),
        change_paramvardecl(5),
        change_paramvardecl_terminal,
        add_include,
      },
      function_found("HandleFunctionDecl6")
    );

  // 関数呼び出しの呼び出し元と呼び出し先の値のマッチング
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
      callExpr(
        unless(isInMacro()),
        unless(isExpansionInSystemHeader()),
        isExpansionInMainFile()
      ).bind("caller"),
      {
        insertBefore(node("caller"), cat("__trace_function_call(")),
        insertAfter(node("caller"), cat(")")),
        add_include,
      },
      cat("HandleCallExpr")
    );

  auto is_function_pointer = implicitCastExpr(hasCastKind(CK_FunctionToPointerDecay));
  auto HandleEachArgumentCallExpr = makeRule(
      stmt(
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        unless(hasAncestor(is_function_pointer)),
        unless(is_function_pointer),
        hasParent(callExpr(unless(isInMacro())))
      ).bind("argument"),
      {
        insertBefore(node("argument"), cat("__trace_function_call_param(")),
        insertAfter(node("argument"), cat(")")),
        add_include,
      },
      cat("HandleEachArgumentCallExpr")
    );

  auto HandleReturnStmt = makeRule(
      returnStmt(
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        hasReturnValue(expr().bind("ReturnValue"))
      ),
      {
        insertBefore(node("ReturnValue"), cat("__trace_function_return(")),
        insertAfter(node("ReturnValue"), cat(")")),
        add_include,
      },
      return_found("HandleReturnStmt")
    );

  return applyFirst({
    HandleFunctionDecl6,
    HandleFunctionDecl5,
    HandleFunctionDecl4,
    HandleFunctionDecl3,
    HandleFunctionDecl2,
    HandleFunctionDecl1,

    HandleEachArgumentCallExpr, // __trace_variable_rvalue と両立しない（例：f(x, 1)）のでChekerを分けている
    HandleCallExpr, // HandleCallExpr と HandleEachArgumentCallExpr の適用位置が被って fix を apply できないことがある
  
    HandleReturnStmt,
  });
}

FunctionCallTracingCheck::FunctionCallTracingCheck(StringRef Name,
                                               ClangTidyContext *Context)
    : utils::TransformerClangTidyCheck(FunctionCallTracingCheckImpl(), Name, Context) {}

} // namespace misc
} // namespace tidy
} // namespace clang
