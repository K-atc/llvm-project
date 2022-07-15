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
  // auto add_include = addInclude("trace.h");

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
  auto HandleFunctionDecl0 = makeRule(
      functionDecl(
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        capture_body
      ),
      {
        change_paramvardecl_begin,
        change_paramvardecl_terminal,
        add_include,
      },
      function_found("HandleFunctionDecl0")
    );
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
  auto HandleFunctionDecl7 = makeRule(
      functionDecl(
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        capture_paramvardecl(0),
        capture_paramvardecl(1),
        capture_paramvardecl(2),
        capture_paramvardecl(3),
        capture_paramvardecl(4),
        capture_paramvardecl(5),
        capture_paramvardecl(6),
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
        change_paramvardecl(6),
        change_paramvardecl_terminal,
        add_include,
      },
      function_found("HandleFunctionDecl7")
    );
  auto HandleFunctionDecl8 = makeRule(
      functionDecl(
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        capture_paramvardecl(0),
        capture_paramvardecl(1),
        capture_paramvardecl(2),
        capture_paramvardecl(3),
        capture_paramvardecl(4),
        capture_paramvardecl(5),
        capture_paramvardecl(6),
        capture_paramvardecl(7),
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
        change_paramvardecl(6),
        change_paramvardecl(7),
        change_paramvardecl_terminal,
        add_include,
      },
      function_found("HandleFunctionDecl8")
    );
  auto HandleFunctionDecl9 = makeRule(
      functionDecl(
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        capture_paramvardecl(0),
        capture_paramvardecl(1),
        capture_paramvardecl(2),
        capture_paramvardecl(3),
        capture_paramvardecl(4),
        capture_paramvardecl(5),
        capture_paramvardecl(6),
        capture_paramvardecl(7),
        capture_paramvardecl(8),
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
        change_paramvardecl(6),
        change_paramvardecl(7),
        change_paramvardecl(8),
        change_paramvardecl_terminal,
        add_include,
      },
      function_found("HandleFunctionDecl9")
    );
  auto HandleFunctionDecl10 = makeRule(
      functionDecl(
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        capture_paramvardecl(0),
        capture_paramvardecl(1),
        capture_paramvardecl(2),
        capture_paramvardecl(3),
        capture_paramvardecl(4),
        capture_paramvardecl(5),
        capture_paramvardecl(6),
        capture_paramvardecl(7),
        capture_paramvardecl(8),
        capture_paramvardecl(9),
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
        change_paramvardecl(6),
        change_paramvardecl(7),
        change_paramvardecl(8),
        change_paramvardecl(9),
        change_paramvardecl_terminal,
        add_include,
      },
      function_found("HandleFunctionDecl10")
    );
  auto HandleFunctionDecl11 = makeRule(
      functionDecl(
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        capture_paramvardecl(0),
        capture_paramvardecl(1),
        capture_paramvardecl(2),
        capture_paramvardecl(3),
        capture_paramvardecl(4),
        capture_paramvardecl(5),
        capture_paramvardecl(6),
        capture_paramvardecl(7),
        capture_paramvardecl(8),
        capture_paramvardecl(9),
        capture_paramvardecl(10),
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
        change_paramvardecl(6),
        change_paramvardecl(7),
        change_paramvardecl(8),
        change_paramvardecl(9),
        change_paramvardecl(10),
        change_paramvardecl_terminal,
        add_include,
      },
      function_found("HandleFunctionDecl11")
    );
  auto HandleFunctionDecl12 = makeRule(
      functionDecl(
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        capture_paramvardecl(0),
        capture_paramvardecl(1),
        capture_paramvardecl(2),
        capture_paramvardecl(3),
        capture_paramvardecl(4),
        capture_paramvardecl(5),
        capture_paramvardecl(6),
        capture_paramvardecl(7),
        capture_paramvardecl(8),
        capture_paramvardecl(9),
        capture_paramvardecl(10),
        capture_paramvardecl(11),
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
        change_paramvardecl(6),
        change_paramvardecl(7),
        change_paramvardecl(8),
        change_paramvardecl(9),
        change_paramvardecl(10),
        change_paramvardecl(11),
        change_paramvardecl_terminal,
        add_include,
      },
      function_found("HandleFunctionDecl12")
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
        isExpansionInMainFile(),
        unless(hasParent(returnStmt())),
        unless(callee(functionDecl(returns(voidType())))),
        callee(expr().bind("callee"))
      ).bind("caller"),
      {
        insertBefore(node("caller"), cat("__trace_function_call(")),
        insertAfter(node("caller"), cat(", ", node("callee"), ")")),
        add_include,
      },
      cat("HandleCallExpr")
    );

  auto HandleVoidCallExpr = makeRule(
      callExpr(
        unless(isInMacro()),
        unless(isExpansionInSystemHeader()),
        isExpansionInMainFile(),
        callee(functionDecl(returns(voidType()))),
        callee(expr().bind("callee"))
      ).bind("caller"),
      {
        insertBefore(node("caller"), cat("__trace_void_function_call(")),
        insertAfter(node("caller"), cat(", ", node("callee"), ")")),
        add_include,
      },
      cat("HandleCallExpr")
    );


/*
|-FunctionDecl 0x2268fb8 </usr/lib/llvm-14/lib/clang/14.0.5/include/stdbool.h:15:14, bad.c:51:1> line:24:6 used test_int 'bool ()'
| `-CompoundStmt 0x226a130 <col:17, line:51:1>
[...]
|   |-CallExpr 0x2269810 <line:37:5, col:8> 'int'
|   | |-ImplicitCastExpr 0x22697f8 <col:5> 'int (*)(int)' <FunctionToPointerDecay>
|   | | `-DeclRefExpr 0x2269788 <col:5> 'int (int)' Function 0x2266ea8 'f' 'int (int)'
|   | `-IntegerLiteral 0x22697a8 <col:7> 'int' 1
*/
  auto HandleCallExprWithUnusedFunctionReturnValue = makeRule(
      callExpr(
        unless(isInMacro()),
        unless(isExpansionInSystemHeader()),
        isExpansionInMainFile(),
        hasParent(compoundStmt()),
        unless(callee(functionDecl(returns(voidType())))),
        callee(expr().bind("callee"))
      ).bind("caller"),
      {
        insertBefore(node("caller"), cat("__trace_function_call(")),
        insertAfter(node("caller"), cat(", ", node("callee"), "); __trace_unused_function_return_value()")),
        add_include,
      },
      cat("HandleCallExprWithUnusedFunctionReturnValue")
    );

  auto is_function_pointer = implicitCastExpr(hasCastKind(CK_FunctionToPointerDecay));
  auto HandleCallExprArgument = makeRule(
      // NOTE: 残念ながら、関数呼び出しをトレースするために CallExpr とマッチしてはいけない
      // callExpr(
      //   forEachArgumentWithParam(
      //     expr().bind("argument"),
      //     parmVarDecl(hasType(type()))
      //   )
      // ),
      stmt(
        unless(isExpansionInSystemHeader()),
        isExpansionInMainFile(),
        unless(is_function_pointer), // FIXME: 引数の関数ポインタが無視される
        hasParent(callExpr(
          unless(isInMacro()),
          unless(hasParent(returnStmt()))
        ))
      ).bind("argument"),
      {
        insertBefore(node("argument"), cat("__trace_function_call_param(")),
        insertAfter(node("argument"), cat(")")),
        add_include,
      },
      cat("HandleCallExprArgument")
    );

/*
|   |-DeclStmt 0x14f1470 <line:62:5, col:34>
|   | `-VarDecl 0x14f1228 <col:5, col:33> col:9 w 'int' cinit
|   |   `-CallExpr 0x14f1448 <col:13, col:33> 'int'
|   |     |-ImplicitCastExpr 0x14f1430 <col:13> 'int (*)(int)' <FunctionToPointerDecay>
|   |     | `-DeclRefExpr 0x14f1290 <col:13> 'int (int)' Function 0x14eab58 'f' 'int (int)'
|   |     `-BinaryOperator 0x14f1410 <col:15, col:32> 'int' '+'
|   |       |-CallExpr 0x14f1308 <col:15, col:20> 'int'
|   |       | |-ImplicitCastExpr 0x14f12f0 <col:15> 'int (*)(int)' <FunctionToPointerDecay>
|   |       | | `-DeclRefExpr 0x14f12b0 <col:15> 'int (int)' Function 0x14eab58 'f' 'int (int)'
|   |       | `-IntegerLiteral 0x14f12d0 <col:17> 'int' 101
|   |       `-CallExpr 0x14f13e8 <col:24, col:32> 'int'
|   |         |-ImplicitCastExpr 0x14f13d0 <col:24> 'int (*)(int)' <FunctionToPointerDecay>
|   |         | `-DeclRefExpr 0x14f1330 <col:24> 'int (int)' Function 0x14eab58 'f' 'int (int)'
|   |         `-CallExpr 0x14f13a8 <col:26, col:31> 'int'
|   |           |-ImplicitCastExpr 0x14f1390 <col:26> 'int (*)(int)' <FunctionToPointerDecay>
|   |           | `-DeclRefExpr 0x14f1350 <col:26> 'int (int)' Function 0x14eab58 'f' 'int (int)'
|   |           `-IntegerLiteral 0x14f1370 <col:28> 'int' 102
*/
  auto HandleFunctionCallCallExprArgument = makeRule(
      callExpr(
        unless(isInMacro()),
        unless(isExpansionInSystemHeader()),
        isExpansionInMainFile(),
        hasParent(callExpr()),
        callee(expr().bind("callee"))
      ).bind("argument"),
      {
        insertBefore(node("argument"), cat("__trace_function_call_param(__trace_function_call(")),
        insertAfter(node("argument"), cat(",", node("callee"), "))")),
        add_include,
      },
      cat("HandleFunctionCallCallExprArgument")
    );

  auto HandleReturnStmt = makeRule(
      returnStmt(
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        hasReturnValue(expr().bind("ReturnValue"))
      ),
      {
        // NOTE: return(ret_val); と書いている例もあるので、安全のためにカッコで囲んでおく
        insertBefore(node("ReturnValue"), cat("(__trace_function_return(")),
        insertAfter(node("ReturnValue"), cat("))")),
        add_include,
      },
      return_found("HandleReturnStmt")
    );

  auto HandleCallExprReturnStmt = makeRule(
      returnStmt(
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        hasReturnValue(callExpr(expr().bind("callee")).bind("ReturnValue"))
      ),
      {
        insertBefore(node("ReturnValue"), cat("(__trace_function_return(__trace_function_call(")),
        insertAfter(node("ReturnValue"), cat(",", node("callee"), ")))")),
        add_include,
      },
      return_found("HandleCallExprReturnStmt")
    );

  return applyFirst({
    HandleFunctionDecl12,
    HandleFunctionDecl11,
    HandleFunctionDecl10,
    HandleFunctionDecl9,
    HandleFunctionDecl8,
    HandleFunctionDecl7,
    HandleFunctionDecl6,
    HandleFunctionDecl5,
    HandleFunctionDecl4,
    HandleFunctionDecl3,
    HandleFunctionDecl2,
    HandleFunctionDecl1,
    HandleFunctionDecl0,

    HandleCallExprReturnStmt,
    HandleReturnStmt,

    // Match with CallExpr
    HandleFunctionCallCallExprArgument,  
    HandleCallExprWithUnusedFunctionReturnValue,
    HandleVoidCallExpr,
    HandleCallExpr, // HandleCallExpr と HandleCallExprArgument の適用位置が被って fix を apply できないことがある

    // Match with stmt
    HandleCallExprArgument, // __trace_variable_rvalue と両立しない（例：f(x, 1)）のでChekerを分けている
  });
}

FunctionCallTracingCheck::FunctionCallTracingCheck(StringRef Name,
                                               ClangTidyContext *Context)
    : utils::TransformerClangTidyCheck(FunctionCallTracingCheckImpl(), Name, Context) {}

} // namespace misc
} // namespace tidy
} // namespace clang
