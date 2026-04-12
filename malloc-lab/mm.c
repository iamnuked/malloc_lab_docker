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

#define MAX(x, y) ((x) > (y) ? (x) : (y))

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


// 가용 리스트 포인터 
#define MAKE_PS_P(bp)
#define PRED_P(bp) ((char *)(bp))
#define SUCC_P(bp) ((char*)(bp) + W_SIZE)


// 분리 가용 리스트 배열 -> 헤드가 들어가있음
typedef struct _seg_free_list {
    size_t min_size;
    size_t max_size;
    void* head;
} seg_free_list;

#define LIST_LIMIT 10
static seg_free_list free_list_head[LIST_LIMIT];

/* 매크로 함수, 상수 */

static void* extend_heap(size_t words);
static void* coalesce(void *bp);
static void* find_fit(size_t a_size);
static void place(void *bp, size_t a_size);


/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void) {

    // 분리 가용 리스트 테이블 만들기
    for(int i = 1; i <= 10; i++) {
        free_list_head[i-1].min_size = 1 << i;
        free_list_head[i-1].max_size = 2 << (i + 1);
    }

    
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
static void* extend_heap(size_t words) {
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


    // 분리 가용 리스트에 저장
    return insert_free_list(coalesce(bp));;
}


// free_list 인덱스 구하기
static int get_list_index(size_t size) {
    int idx = 0;

    while (idx < LIST_LIMIT - 1 && size > 1) {
        size >>= 1;
        idx++;
    }

    return idx;
}

// free_list 추가
static void* insert_free_list(void* ptr) {
    int idx = get_list_index(GET_BLOCK_SIZE(ptr));
    PUT(free_list_head[idx].head + W_SIZE, ptr);// 1번 head + 4 위치 값을 ptr 주소로 저장
    ptr = free_list_head[idx].head;             // 2번 head 주소 ptr에 저장
    free_list_head[idx].head = ptr;             // 3번 head 값을 ptr로 저장

    return ptr;
}

// 할당 시 free list에서 삭제
static void* remove_free_list(void* ptr) {
    int idx = get_list_index(GET_BLOCK_SIZE(ptr));

}



/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) {
    size_t a_size;
    size_t extendsize;
    char *bp;

    if(size == 0) return NULL;

    if(size <= DW_SIZE) {
        a_size = 2*DW_SIZE;   
    } 
    else {
        a_size = DW_SIZE * ((size + (DW_SIZE) + (DW_SIZE-1)) / DW_SIZE);
    }

    if((bp = find_fit(a_size)) != NULL) {
        place(bp, a_size);
        return bp;
    }

    extendsize = MAX(a_size, CHUNK_SIZE);
    if((bp = extend_heap(extendsize/W_SIZE)) == NULL) return NULL;
    place(bp, a_size);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr) {
    size_t size = GET_BLOCK_SIZE(HDR_P(ptr));

    PUT(HDR_P(ptr), MAKE_H_F(size, 0));
    PUT(FTR_P(ptr), MAKE_H_F(size, 0));
    insert_free_list(coalesce(ptr)); // 병합 후 가용 리스트 추가
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




static void *coalesce(void *bp) {
    size_t prev_alloc = GET_IS_ALLOC(FTR_P(PREV_BLOCK_P(bp)));
    size_t next_alloc = GET_IS_ALLOC(HDR_P(NEXT_BLOCK_P(bp)));
    size_t size = GET_BLOCK_SIZE(HDR_P(bp));

    // 앞 뒤 다 사용중일 경우
    if(prev_alloc && next_alloc) return bp;
    // 뒤랑 병합
    else if(prev_alloc && !next_alloc) {
        size += GET_BLOCK_SIZE(HDR_P(NEXT_BLOCK_P(bp)));
        PUT(HDR_P(bp), MAKE_H_F(size, 0));
        PUT(FTR_P(bp), MAKE_H_F(size, 0));
    }
    // 앞이랑 병합
    else if(!prev_alloc && next_alloc) {
        size += GET_BLOCK_SIZE(HDR_P(PREV_BLOCK_P(bp)));
        PUT(HDR_P(PREV_BLOCK_P(bp)), MAKE_H_F(size, 0));
        PUT(FTR_P(bp), MAKE_H_F(size, 0));
        bp = PREV_BLOCK_P(bp);
    }
    // 둘 다 병합
    else {
        size += GET_BLOCK_SIZE(HDR_P(PREV_BLOCK_P(bp))) + GET_BLOCK_SIZE(HDR_P(NEXT_BLOCK_P(bp)));

        PUT(HDR_P(PREV_BLOCK_P(bp)), MAKE_H_F(size, 0));
        PUT(FTR_P(NEXT_BLOCK_P(bp)), MAKE_H_F(size, 0));
        bp = PREV_BLOCK_P(bp);
    }
    return bp;
}

static void* find_fit(size_t a_size) {
    void *bp;

    for(bp = mem_start_brk; GET_BLOCK_SIZE(HDR_P(bp)) > 0; bp = NEXT_BLOCK_P(bp)) {
        if(!GET_IS_ALLOC(HDR_P(bp)) && (a_size <= GET_BLOCK_SIZE(HDR_P(bp)))) {
            return bp;
        }
    }
    return NULL;
}

static void place(void *bp, size_t a_size) {
    size_t c_size = GET_BLOCK_SIZE(HDR_P(bp));

    if((c_size - a_size) >= (2*DW_SIZE)) {
        PUT(HDR_P(bp), MAKE_H_F(a_size, 1));
        PUT(FTR_P(bp), MAKE_H_F(a_size, 1));
        bp = NEXT_BLOCK_P(bp);
        PUT(HDR_P(bp), MAKE_H_F(c_size - a_size, 1));
        PUT(FTR_P(bp), MAKE_H_F(a_size - a_size, 1));
    }
    else {
        PUT(HDR_P(bp), MAKE_H_F(c_size, 1));
        PUT(FTR_P(bp), MAKE_H_F(c_size, 1));
    }
}