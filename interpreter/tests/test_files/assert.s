_init:
    mov r1 r31          ; r1 = (RWX, init, end, init)
    lea r1 (_assert_data-init)	; r1 = (RWX, init, end, assertdata)
    subseg r1 _assert_data _assert_end 	; r1 = (RWX, assert_data, end_assert, assert_data)
    restrict r1 RW GLOBAL                      ; r1 = (RW, assert_data, end_assert, assert_data)
    store r1 r1
    lea r1 1
    store r1 0                  ; init the flag at 0
_end_init:
_assert:
    sub r4 r4 r5
    mov r5 pc
    lea r5 6
    jnz r5 r4
    mov r4 0
    mov r5 0
    jmp r0; (* return *)
    lea r5 6; (* pointer to cap: *)
    load r5 r5
    store r5 1
    mov r4 0
    mov r5 0
    jmp r0     ; return
_assert_data:
    jmp pc ; dummy data, (RW, flag, end, flag)
    jmp pc ; dummy data, flag <0 or 1>
_assert_end:
