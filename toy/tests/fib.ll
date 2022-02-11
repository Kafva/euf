target triple = "x86_64-pc-linux-gnu"
; The language: https://llvm.org/docs/LangRef.html
; Global identifiers '@'
; Local identifiers '%'
; Metadata '!'
; Attribute groups '#'

; Each module effecitvly corresponds to a TU

; 'internal' limits the scope of variable to the current TU
@.str = private constant [4 x i8] c"%d\0A\00"

declare i32 @printf(i8*, ...)

define i32 @fib(i32 %k) #0 {
  ; The return value can be either a vector of boolean
  ; or a single boolean depending on the arguments
  ; 'sle' ~ signed less or equal
  %res0 = icmp sle i32 %k, 1 ; %k <= 1

  ; %cond %iftrue, %iffalse
  br i1 %res0, label %base-case, label %recurse 

base-case:
  ret i32 1

recurse:
  ; op lhs rhs
  %decr    = sub i32 %k, 1 ; k - 1
  %res1    = call i32 (i32) @fib(i32 %decr)
  ; We cannot re-use the same variable name several times
  ; since that would violate SSA
  %res2    = add i32 %res1, %k
  ret i32 %res2
}

define i32 @main() #0 { 

  %y = call i32 (i32) @fib(i32 9)

  ; The GEP instruction is used to get the address of a 'subelement'
  ; in a aggregate datastructure, similar to `lea`
  ; Like many other functions, getelementptr has a 'vector' version
  ;
  ; The first argument corresponds to the type of element we are indexing
  ; in this case a static 4 element vector
  ;
  ; The second argument is the type of the third argument
  ; The third argument is our base address
  ;
  ; The last two arguments are indices into:
  ;   The pointer (because GEP is only defined for pointers)
  ;   The index in the actual array
  %_ = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str, i64 0, i64 0),  i32 %y)

  ret i32 0
}



; The attributes for all functions in group #0
;
; nocapture: A function performs a pointer capture if it saves some part
; of the pointer's address to a location that persists after
; the call (e.g. a global variable)
;
; nounwind: The function will not raise an exception (N/A for pure C)
attributes #0 = { nounwind  }
