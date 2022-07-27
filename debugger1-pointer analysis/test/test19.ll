; ModuleID = 'test19.c'
source_filename = "test19.c"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %stop = alloca i32, align 4
  %point = alloca i32*, align 8
  %a = alloca i32, align 4
  %b = alloca i32, align 4
  %c = alloca i32, align 4
  %d = alloca i32, align 4
  %e = alloca i32*, align 8
  %f = alloca i32*, align 8
  %y = alloca i32, align 4
  store i32 0, i32* %retval, align 4
  %call = call i32 @getchar()
  store i32 %call, i32* %stop, align 4
  %0 = load i32, i32* %stop, align 4
  %cmp = icmp sgt i32 %0, 4
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  store i32 2, i32* %stop, align 4
  br label %if.end

if.end:                                           ; preds = %if.then, %entry
  store i32* null, i32** %point, align 8
  store i32 1, i32* %a, align 4
  store i32 2, i32* %b, align 4
  store i32 0, i32* %c, align 4
  store i32 3, i32* %d, align 4
  %1 = load i32, i32* %stop, align 4
  %cmp1 = icmp eq i32 %1, 0
  br i1 %cmp1, label %if.then2, label %if.else

if.then2:                                         ; preds = %if.end
  store i32* %a, i32** %point, align 8
  br label %if.end11

if.else:                                          ; preds = %if.end
  %2 = load i32, i32* %stop, align 4
  %cmp3 = icmp eq i32 %2, 1
  br i1 %cmp3, label %if.then4, label %if.else5

if.then4:                                         ; preds = %if.else
  store i32* %b, i32** %point, align 8
  br label %if.end10

if.else5:                                         ; preds = %if.else
  %3 = load i32, i32* %stop, align 4
  %cmp6 = icmp eq i32 %3, 2
  br i1 %cmp6, label %if.then7, label %if.else8

if.then7:                                         ; preds = %if.else5
  store i32* %c, i32** %point, align 8
  br label %if.end9

if.else8:                                         ; preds = %if.else5
  store i32* %d, i32** %point, align 8
  br label %if.end9

if.end9:                                          ; preds = %if.else8, %if.then7
  br label %if.end10

if.end10:                                         ; preds = %if.end9, %if.then4
  br label %if.end11

if.end11:                                         ; preds = %if.end10, %if.then2
  store i32* %a, i32** %e, align 8
  store i32* %a, i32** %f, align 8
  %4 = load i32*, i32** %f, align 8
  %5 = load i32, i32* %4, align 4
  %6 = load i32*, i32** %point, align 8
  %7 = load i32, i32* %6, align 4
  %div = sdiv i32 %5, %7
  store i32 %div, i32* %y, align 4
  ret i32 0
}

declare dso_local i32 @getchar() #1

attributes #0 = { noinline nounwind uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{!"clang version 8.0.1- (branches/release_80)"}
