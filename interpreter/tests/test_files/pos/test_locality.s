code:
    mov r0 pc                   ; r0 Global - without WL
    lea r0 data
    storeU stk 0 0              ; Derive a non-U, WL, Local capabality from stk
    storeU stk 0 0
    promoteU stk
    lea stk -2
    store r0 r0                ; We can store global without WL
    store stk r0               ; We can store global with WL
    lea stk 1
    store stk stk                   ; We can store local with WL
    restrict r0 RWX GLOBAL          ; Global can be restricted to global
    restrict r0 RWX LOCAL          ; Global can be restricted to local
    restrict r0 RWX LOCAL          ; Local can be restricted to local
    halt
data:
