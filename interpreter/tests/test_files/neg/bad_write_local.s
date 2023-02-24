    ;; try to write a local cap without WL permission
	mov r0 pc
    mov r1 pc
    restrict r1 O LOCAL
    store r0 r1
	halt
