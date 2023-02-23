init:
	mov r31 pc          ; r31 = (RWX, init, end, init) ; just to remember
    ;; init linking table
    mov r30 r31         ; r30 = (RWX, init, end, init)
    lea r30 (slinkingtable-init) ; r30 = (RWX, init, end, slink)
	subseg r30 slinkingtable elinkingtable 	; r1 = (RWX, slink, elink, slink)
    ;; init malloc
    mov r1 r31          ; r1 = (RWX, init, end, init)
	lea r1 (bmid-init)	; r1 = (RWX, init, end, bmid)
	subseg r1 bmid em 	; r1 = (RWX, bmid, em, bmid)
    mov r2 r1           ; r2 = (RWX, init, end, bmid)
    lea r2 1            ; r2 = (RWX, init, end, am)
    store r1 r2         ; store the capability at bmid
    mov r2 0            ; clear r2
    ;; closure malloc
    mov r1 r31                  ; r1 = (RWX, init, end, init)
    lea r1 (malloc-init)	    ; r1 = (RWX, init, end, malloc)
	subseg r1 malloc em 	    ; r1 = (RWX, malloc, em, malloc)
    restrict r1 E GLOBAL               ; r1 = (E, malloc, em, malloc)
    ;; store malloc
    store r30 r1

    ;; init assert
    mov r1 r31          ; r1 = (RWX, init, end, init)
	lea r1 (assertdata-init)	; r1 = (RWX, init, end, assertdata)
	subseg r1 assertdata assertend 	; r1 = (RWX, assert_data, end_assert, assert_data)
    restrict r1 RW GLOBAL                      ; r1 = (RW, assert_data, end_assert, assert_data)
    store r1 r1
    lea r1 1
    store r1 0                  ; init the flag at 0
    ;; closure assert
    mov r1 r31                  ; r1 = (RWX, init, end, init)
    lea r1 (assert-init)	    ; r1 = (RWX, init, end, assert)
	subseg r1 assert assertend 	    ; r1 = (RWX, assert, end_assert, assert)
    restrict r1 E GLOBAL               ; r1 = (E, assert, end_assert, assert)
    ;; store assert
    lea r30 1
    store r30 r1
    lea r30 -1
    ;; restrict linking table capability
    restrict r30 RO GLOBAL

    ;; closure code
    mov r0 r31          ; r0 = (RWX, init, end, init)
	lea r0 (data-init)	; r0 = (RWX, init, end, data)
    store r0 r30        ; store linking_table cap
    lea r0 (code-data) ; r0 = (RWX, init, end, code)
	subseg r0 data endcode ; r0 = (RWX, data, endcode, code)
    restrict r0 E GLOBAL     ; r0 = (E, data, endcode, code+1)
    ;; clear registers and jump
    mov r1 0
    mov r30 0
    mov r31 0
    jmp r0
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
endcode:

slinkingtable:
    jmp pc ; dummy data, entry malloc
    jmp pc ; dummy data, entry assert
elinkingtable:

assert:
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
assertdata:
    jmp pc ; dummy data, (RW, flag, end, flag)
    jmp pc ; dummy data, flag <0 or 1>
assertend:
malloc:
    lt r3 0 r1
    mov r2 pc
    lea r2 4
    jnz r2 r3
    fail
    mov r2 pc
    lea r2 21 ; size subroutine
    load r2 r2
    geta r3 r2
    lea r2 r1
    geta r1 r2
    mov r4 r2
    subseg r4 r3 r1
    sub r3 r3 r1
    lea r4 r3
    mov r3 r2
    sub r1 0 r1
    lea r3 r1
    getb r1 r3
    lea r3 r1
    store r3 r2
    mov r1 r4
    mov r2 0
    mov r3 0
    mov r4 0
    jmp r0
bmid:
    jmp pc                    ; dummy data, for capabilibity (RWX, bmid, em, a)
am:
    jmp pc ; dummy data
    jmp pc ; dummy data
    jmp pc ; dummy data
    jmp pc ; dummy data
    jmp pc ; dummy data
    jmp pc ; dummy data
    jmp pc ; dummy data
    jmp pc ; dummy data
    jmp pc ; dummy data
    jmp pc ; dummy data
    jmp pc ; dummy data
    jmp pc ; dummy data
    jmp pc ; dummy data
    jmp pc ; dummy data
    jmp pc ; dummy data
    jmp pc ; dummy data
    jmp pc ; dummy data
    jmp pc ; dummy data
    jmp pc ; dummy data
    jmp pc ; dummy data
em:
end:
