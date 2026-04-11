/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))


/* 매크로 함수, 상수 */

#define W_SIZE 4 // 워드 사이즈
#define DW_SIZE 8 // 더블워드 사이즈
#define CHUNK_SIZE (1<<12) // 4KB

// 헤더 or 풋터 만들기
#define MAKE_H_F(b_size, isAllocated) ((b_size) | (isAllocated))

// 해당 위치 value 가져오기
#define GET(p) (*(unsigned int*)(p))
// 해당 위치에 value 저장하기
#define PUT(p, val) ( (*(unsigned int*)(p)) = (val) )

// 헤더 or 풋터에서 블럭 사이즈 가져오기
#define GET_BLOCK_SIZE(p) (GET(p) & ~0x7)
// 헤더 or 풋터에서 할당 여부 플래그값 가져오기
#define GET_IS_ALLOC(p) (GET(p) & 0x1)


// bp 는 블럭 포이터를 뜻함 블럭 포인터는 헤더가 아닌 페이로드 시작 주소를 가리킴
#define HDR_P(bp) ( (char *)(bp) - W_SIZE )
#define FTR_P(bp) ( (char *)(bp) + GET_BLOCK_SIZE(HDR_P(bp)) - DW_SIZE )

#define NEXT_BLOCK_P(bp) ( (char *)(bp) + GET_BLOCK_SIZE(( (char *)(bp) - W_SIZE)) )
#define PREV_BLOCK_P(bp) ( (char *)(bp) - GET_BLOCK_SIZE(( (char *)(bp) - DW_SIZE)) )


/* 매크로 함수, 상수 */


/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void) {
    
    // 16만큼 할당, mem_sbrk는 이전 포인터 반환해줌
    if( (mem_start_brk = mem_sbrk(4 * W_SIZE)) == (void *)-1 ) return -1;
    // unused padding 추가 작업
    PUT(mem_start_brk, 0);

    // prologue hdr
    PUT(mem_start_brk + (1*W_SIZE), MAKE_H_F(DW_SIZE, 1));

    // prologue ftr
    PUT(mem_start_brk + (2*W_SIZE), MAKE_H_F(DW_SIZE, 1));

    // epilogue hdr
    PUT(mem_start_brk + (3*W_SIZE), MAKE_H_F(0, 1));

    // prologue block pointer로 위치시키기
    mem_start_brk += (2*W_SIZE);

    if(extend_heap(CHUNK_SIZE/W_SIZE) == NULL) return -1;

    return 0;
}


// 힙 공간 늘리기 -> 새로 가용 블록 생성 후 이전 블록과 병합할 수 있으면 병합
void* extend_heap(size_t words) {
    char* bp;
    size_t size;

    // words를 짝수로 맞추면 size는 8의 배수로 됨 -> W_SIZE가 4이기 때문
    size = (words % 2) ? (words+1) * W_SIZE : words * W_SIZE;
    if((long)(bp = mem_sbrk(size)) == -1) return NULL;


    // 추가된 가용 영역 헤더 풋터 생성
    PUT(HDR_P(bp), MAKE_H_F(size, 0));
    PUT(FTR_P(bp), MAKE_H_F(size, 0));
    
    // 새로 epilog hdr 생성
    PUT(HDR_P(NEXT_BLOCK_P(bp)), MAKE_H_F(0, 1));


    return coalesce(bp);
}


/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) {
    int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);
    if (p == (void *)-1)
        return NULL;
    else
    {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr) {

}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}




