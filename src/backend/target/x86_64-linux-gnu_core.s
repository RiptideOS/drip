; This file includes core functions required for the drip runtime. These are 
; temporary until we get inline assembly to do this instead.

bits 64
section .text

; Takes a pointer to UTF-8 data and a length (the fields of a str) 
; and performs a write syscall to STDOUT
;
; @input rdi - pointer to string data
; @input rsi - length in bytes
; @output rax - value returned from write syscall
__$print_str:
    push rdi
    push rsi 
    push rdx

    mov rdx, rsi ; len
    mov rsi, rdi ; ptr
    mov rax, 1   ; syscall # = write
    mov rdi, 1   ; fd = stdout
    syscall

    pop rdx
    pop rsi 
    pop rdi
    ret

; Takes a i8 ASCII char and performs a write syscall to STDOUT
;
; @input rdi - i8 char
; @output rax - value returned from write syscall
__$print_ascii_char:
    push rbp
    mov rbp, rsp
    push rdi
    push rsi
    push rdx
    
    ; store the character on the stack
    sub rsp, 1
    mov rax, rdi
    mov byte [rbp - 1], al

    ; write syscall
    mov rax, 1         ; syscall # = write
    mov rdi, 1         ; fd = stdout
    lea rsi, [rbp - 1] ; ptr = stack addr of char byte
    mov rdx, 1         ; len = 1 

    pop rdx
    pop rsi
    pop rdi
    mov rsp, rbp
    pop rbp
    ret

; Takes an i32 and prints it to STDOUT in hex format without leading zeros :)
;
; @input rdi - the i32 to print
; @output rax - value returned from write syscall
__$print_i32_hex:
    push rbp
    mov rbp, rsp
    push rbx
    push rcx
    push rdi
    push rsi

    ; Special case for zero
    cmp rdi, 0
    jne .loop_start
    mov rdi, '0'
    call __$print_ascii_char
    jmp .exit

    ; reserve room on the stack for the buffer we will be printing
    sub rsp, 8

    xor rcx, rcx ; leading zero counter
    xor rdx, rdx ; loop counter

    ; Iterate the digits of the number from highest to lowest and 
    ; push the chars onto the stack
    .loop_start:
        ; isolate the bottom 4 bits in rbx
        xor rbx, rbx
        mov rbx, rdi
        and rbx, 0xF 

        ; convert the nibble to hex and push its ascii char onto 
        ; the stack buffer
        mov byte al, [.table + rbx]
        mov rsi, rbp
        sub rsi, rdx
        mov byte [rsi], al

        ; keep track of the last digit which was not a zero
        cmp rbx, 0
        je .is_zero

    ; reset the leading zero counter each time we see a non-zero character
    .not_zero:
        mov rcx, 0
        jmp .loop_wrap

    ; increment rcx each time we see a zero character
    .is_zero:
        inc rcx

    ; shift right and check if there are digits left
    .loop_wrap:
        inc rdx 

        shr rdi, 4
        test rdi, rdi
        jnz .loop_start

    ; Print the characters we pushed onto the stack and ignore leading zeros
    .print_chars:
        ; stack pointer points to the start of the string, so add 
        ; the number leading zeros we counted to skip them
        lea rdi, [rbp - 8 + rcx] 

        ; number of chars is rbp - rsp + rcx
        mov rsi, rbp
        sub rsi, rsp
        add rsi, rcx

        call __$print_str

    .exit:
        pop rsi
        pop rdi
        pop rcx
        pop rbx
        mov rsp, rbp
        pop rbp
        ret

    ; lookup table for converting numbers 0-15 to hex characters
    .table: db "0123456789abcdef"


__$syscall_1:
    ; TODO

__$syscall_2:
    ; TODO

__$syscall_3:
    ; TODO

__$syscall_4:
    ; TODO

__$syscall_5:
    ; TODO

__$syscall_6:
    ; TODO