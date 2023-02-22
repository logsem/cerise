data:
    jmp pc                      ; dummy data, for linking_table
code:
    mov r0 0                     ; for linking_table
    ;; allocation of buffer
    ;; 1) fetch
    mov r1 pc
    getb r2 r1
    geta r3 r1
    sub r2 r2 r3
    lea r1 r2
    load r1 r1
    lea r1 0                    ; entry of malloc = 0
    mov r2 0
    mov r3 0
    load r1 r1
    ;; 2) call malloc
    mov r5 r0
    mov r3 r1
    mov r1 5                 ; size of allocation
    mov r0 pc
    lea r0 3
    jmp r3
    mov r0 r5
    mov r5 0
    ;; use the allocated memory
    store r1 1
    lea r1 1
    store r1 2
    lea r1 1
    store r1 3
    lea r1 1
    store r1 4
    lea r1 1
    store r1 5
    mov r31 r1                  ; copy the capability to the 1st buffer

    ;; allocation another buffer
    ;; 1) fetch
    mov r1 pc
    getb r2 r1
    geta r3 r1
    sub r2 r2 r3
    lea r1 r2
    load r1 r1
    lea r1 0                    ; entry of malloc = 0
    mov r2 0
    mov r3 0
    load r1 r1
    ;; 2) call malloc
    mov r5 r0
    mov r3 r1
    mov r1 3                 ; size of allocation 3
    mov r0 pc
    lea r0 3
    jmp r3
    mov r0 r5
    mov r5 0

    ;; use assert to check idk ?

    halt
end:
