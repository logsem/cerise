code:
    mov r0 pc                   ; r0 Global

    restrict r0 RWX GLOBAL          ; Global can be restricted to global
    restrict r0 RWX LOCAL           ; Global can be restricted to local
    restrict r0 RWX LOCAL           ; Local can be restricted to local
    restrict r0 RWX DIRECTED        ; Local can be restricted to directed
    restrict r0 RWX DIRECTED        ; Directed can be restricted to directed

    mov r0 pc                       ; r0 Global
    restrict r0 RWX DIRECTED        ; Global can be restricted to directed
    halt
data:
