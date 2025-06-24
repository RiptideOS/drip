; This file includes core functions required for the drip runtime. These are 
; temporary until we get inline assembly to do this instead.

bits 64
section .text

global __$print_str

; Takes a pointer to UTF-8 data and a length (the fields of a str) 
; and performs a write syscall to STDOUT
;
; @input rdi - pointer to string data
; @input rsi - length in bytes
; @output rax - value returned from write syscall
__$print_str:
    mov rdx, rsi ; len
    mov rsi, rdi ; ptr
    mov rax, 1   ; syscall # = write
    mov rdi, 1   ; fd = stdout
    syscall

    ret

global __$print_ascii_char

; Takes a i8 ASCII char and performs a write syscall to STDOUT
;
; @input rdi - i8 char
; @output rax - value returned from write syscall
__$print_ascii_char:
    push rbp
    mov rbp, rsp

    ; store the character on the stack
    sub rsp, 1
    mov rax, rdi
    mov byte [rbp - 1], al

    ; write syscall
    mov rax, 1         ; syscall # = write
    mov rdi, 1         ; fd = stdout
    lea rsi, [rbp - 1] ; ptr = stack addr of char byte
    mov rdx, 1         ; len = 1 
    syscall

    mov rsp, rbp
    pop rbp
    ret

global __$print_i64_hex

; Takes an i64 and prints it to STDOUT in hex format without leading zeros :)
;
; @input rdi - the i64 to print
; @output rax - value returned from write syscall
__$print_i64_hex:
    push rbx
    push rbp
    mov rbp, rsp

    ; reserve room on the stack for the buffer we will be printing
    sub rsp, 16

    ; loop counter
    xor rdx, rdx

    ; Iterate the digits of the number from highest to lowest and
    ; push the chars onto the stack
    .loop_wrap:
        ; isolate the bottom 4 bits in rbx
        xor rbx, rbx
        mov rbx, rdi
        and rbx, 0xF

        ; convert the nibble to hex and push its ascii char onto
        ; the stack buffer
        mov byte al, [.table + rbx]
        lea rsi, [rbp - 1]
        sub rsi, rdx
        mov byte [rsi], al

    ; shift right and check if there are digits left
    .loop_condition:
        inc rdx

        shr rdi, 4
        cmp rdi, 0
        jne .loop_wrap

    ; Print the characters we pushed onto the stack and ignore leading zeros
    .print_chars:
        ; stack pointer points to the start of the string, so add 
        ; the number leading zeros we counted to skip them
        mov rdi, rbp
        sub rdi, rdx

        ; number of chars is rdx
        mov rsi, rdx

        call __$print_str

    .exit:
        mov rsp, rbp
        pop rbp
        pop rbx
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