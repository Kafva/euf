; The language: https://llvm.org/docs/LangRef.html
; Global identifiers '@'
; Local identifiers '%'
; Metadata '!'
; Attribute groups '#'

; Each module effecitvly corresponds to a TU

@.str = private unnamed_addr constant [4 x i8] c"%d\0A\00"

; nocapture: A function performs a pointer capture if it saves some part
; of the pointer's address to a location that persists after
; the call (e.g. a global variable)
;
; nounwind: The function will not raise an exception (N/A for pure C)
declare i32 @puts(i32 nocapture) nounwind

declare i32 @printf(i8*, ...)

define i32 @main() #0 { 

  %x = add i32 9, 9
  call i32 @putchar(i32 %x)

  ret i32 0
}


; The attributes for all functions in group #0
attributes #0 = { nounwind }
