; RUN: opt -disable-output -passes=derive-smt %s 2>&1 | FileCheck %s
; Place in: llvm/test/Analysis/Utils/derivesmt.ll

; CHECK: {{^}}foo{{$}}
define dso_local i32 @foo() {
  %a = add i32 2, 3
  ret i32 %a
}

; CHECK-NEXT: {{^}}bar{{$}}
define void @bar() {
  ret void
}
