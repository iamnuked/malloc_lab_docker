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
    "ROOM303-TEAM4",
    /* First member's full name */
    "BEOM JIN JEONG",
    /* First member's email address */
    "qjawls6262@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* 64비트 기준으로 정렬 16으로 변경 */
#define ALIGNMENT 16

/* 요청 크기 16배수로 맞춰주기 */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0xf)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) < (y) ? (x) : (y))

#define W_SIZE 8 // 워드 사이즈
#define DW_SIZE 16 // 더블워드 사이즈
#define CHUNK_SIZE (1<<5) // 4KB


// 해당 위치 value 가져오기
#define GET(p) (*(size_t *)(p))
// 해당 위치에 value 저장하기
#define PUT(p, val) ( (*(size_t *)(p)) = (size_t)(val) )

// 헤더 or 풋터에서 블럭 사이즈 가져오기
#define GET_BLOCK_SIZE(p) (GET(p) & ~0xf)
// 헤더 or 풋터에서 할당 여부 플래그값 가져오기
#define GET_IS_ALLOC(p) (GET(p) & 0x1)


// bp 는 블럭 포이터를 뜻함 블럭 포인터는 헤더가 아닌 페이로드 시작 주소를 가리킴
#define HDR_P(bp) ( (char *)(bp) - W_SIZE )
#define FTR_P(bp) ( (char *)(bp) + GET_BLOCK_SIZE(HDR_P(bp)) - DW_SIZE )

#define NEXT_BLOCK_P(bp) ( (char *)(bp) + GET_BLOCK_SIZE(( (char *)(bp) - W_SIZE)) )
#define PREV_BLOCK_P(bp) ( (char *)(bp) - GET_BLOCK_SIZE(( (char *)(bp) - DW_SIZE)) )


// 헤더 or 풋터 내용 채워넣기
#define MAKE_H_F(b_size, isAllocated) ((b_size) | (isAllocated))

// 헤더와 풋터 넣기
#define INSERT_H(p, b_size, isAllocated) (PUT((HDR_P(p)), MAKE_H_F((b_size), (isAllocated))))
#define INSERT_F(p, b_size, isAllocated) (PUT((FTR_P(p)), MAKE_H_F((b_size), (isAllocated))))


// 가용 리스트 포인터 
#define PRED_P(bp) ((char *)(bp))
#define SUCC_P(bp) ((char*)(bp) + W_SIZE)



// 분리 가용 리스트 배열 -> 헤드가 들어가있음
typedef struct _seg_free_list {
    size_t min_size;
    size_t max_size;
    void* head;
} seg_free_list;

#define LIST_LIMIT 20
static seg_free_list free_list_head[LIST_LIMIT];



/* 매크로 함수, 상수 */

static void* extend_heap(size_t words);
static void* coalesce(void* bp);
static void* first_fit(size_t a_size);
static void place(void* bp, size_t a_size);
static void* insert_free_list(void* bp);

/*
 * mm_init - initialize the malloc package.
 */
// 완성
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

    // 분리 가용 리스트 테이블 만들기
    for(int i = 1; i <= LIST_LIMIT; i++) {
        free_list_head[i-1].min_size = 1 << i;
        free_list_head[i-1].max_size = 2 << (i + 1);
        free_list_head[i-1].head = NULL;
    }

    if(extend_heap(CHUNK_SIZE/W_SIZE) == NULL) return -1;

    return 0;
}


// 힙 공간 늘리기 -> 새로 가용 블록 생성 후 이전 블록과 병합할 수 있으면 병합
static void* extend_heap(size_t words) {
    char* bp;
    size_t size;

    // words를 짝수로 맞추면 size는 16의 배수로 됨 -> W_SIZE가 8이기 때문
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


// 할당 시 free list에서 삭제
static void* remove_free_list(void* bp) {
    int idx = get_list_index(GET_BLOCK_SIZE(HDR_P(bp)));
    void *prev = (void*)GET(PRED_P(bp));
    void *next = (void*)GET(SUCC_P(bp));

    if(prev != NULL) {
        PUT(SUCC_P(prev), next);
    }
    else {
        free_list_head[idx].head = next;
    }

    if(next != NULL) {
        PUT(PRED_P(next), prev);
    }
    return bp;
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

    // best로 수정
    if((bp = first_fit(a_size)) != NULL) {
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

void *mm_realloc(void *old_bp, size_t req_size) {

    if(old_bp == NULL) {
        return mm_malloc(req_size);
    }

    if(req_size == 0) {
        mm_free(old_bp);
        return NULL;
    }

    void* new_bp = old_bp; // 임시: 앞 블럭과 병합하면 앞 블럭으로 이동
    size_t old_b_size = GET_BLOCK_SIZE(HDR_P(old_bp));
    size_t c_size = old_b_size; // 임시: 앞, 뒤 병합 후 진짜 c_size
    size_t a_size; // 조정된 블럭 사이즈즈 req_size 기준으로 16배수로 조정
    void* prev_bp = PREV_BLOCK_P(old_bp);
    void* next_bp = NEXT_BLOCK_P(old_bp);

    char is_alloc_flag[2] = {0, 0};

    if(req_size <= DW_SIZE) { // 16배수로 조정 -> a_size = 새로운 블럭 사이즈
            a_size = 2*DW_SIZE;   
    }
    else {
        a_size = DW_SIZE * ((req_size + (DW_SIZE) + (DW_SIZE-1)) / DW_SIZE);
    }

    
    // 1. check prev -> is_alloc, block_size
    if(!GET_IS_ALLOC(HDR_P(prev_bp))) {
        c_size += GET_BLOCK_SIZE(HDR_P(prev_bp));
        is_alloc_flag[0]++;
    }

    // 2. check next -> is_alloc, block_size
    if(!GET_IS_ALLOC(HDR_P(next_bp))) {
        c_size += GET_BLOCK_SIZE(HDR_P(next_bp));
        is_alloc_flag[1]++;
    }


    // 3. compair size 
    if(a_size <= c_size) {
        if(is_alloc_flag[0] == 1) {
            new_bp = prev_bp; // 새로 할당받을 블럭 주소를 이전 블럭 주소로 변경
            remove_free_list(prev_bp);
        }
        if(is_alloc_flag[1] == 1) {
            remove_free_list(next_bp);
        }

        // 메로리 할당
        memmove(new_bp, old_bp, MIN(old_b_size-DW_SIZE, req_size)); // 영역 겹칠 경우 대비

        if((c_size - a_size) >= (4*W_SIZE)) {
            INSERT_H(new_bp, a_size, 1);
            INSERT_F(new_bp, a_size, 1);

            // 분리된 공간 가용 영역으로 만들기
            next_bp = NEXT_BLOCK_P(new_bp);
            INSERT_H(next_bp, c_size - a_size, 0);
            INSERT_F(next_bp, c_size - a_size, 0);
            insert_free_list(next_bp);
        }
        else {
            INSERT_H(new_bp, c_size, 1);
            INSERT_F(new_bp, c_size, 1);
        }

        
    }
    else {
        new_bp = mm_malloc(req_size);
        memcpy(new_bp, old_bp, MIN(old_b_size-DW_SIZE, req_size));
        mm_free(old_bp);
    }
    return new_bp;
}



// 병합
static void *coalesce(void *bp) {
    size_t prev_alloc = GET_IS_ALLOC(FTR_P(PREV_BLOCK_P(bp)));
    size_t next_alloc = GET_IS_ALLOC(HDR_P(NEXT_BLOCK_P(bp)));
    size_t size = GET_BLOCK_SIZE(HDR_P(bp));

    // 앞 뒤 다 사용중일 경우
    if(prev_alloc && next_alloc) return bp;
    // 뒤랑 병합
    else if(prev_alloc && !next_alloc) {
        void* next_bp = NEXT_BLOCK_P(bp);
        remove_free_list(next_bp);

        size += GET_BLOCK_SIZE(HDR_P(next_bp));
        PUT(HDR_P(bp), MAKE_H_F(size, 0));
        PUT(FTR_P(bp), MAKE_H_F(size, 0));
    }
    // 앞이랑 병합
    else if(!prev_alloc && next_alloc) {
        void* prev_bp = PREV_BLOCK_P(bp);
        remove_free_list(prev_bp);

        size += GET_BLOCK_SIZE(HDR_P(prev_bp));
        PUT(HDR_P(prev_bp), MAKE_H_F(size, 0));
        PUT(FTR_P(bp), MAKE_H_F(size, 0));
        bp = prev_bp;
    }
    // 둘 다 병합
    else {
        void* next_bp = NEXT_BLOCK_P(bp);
        void* prev_bp = PREV_BLOCK_P(bp);
        remove_free_list(next_bp);
        remove_free_list(prev_bp);
        
        size += GET_BLOCK_SIZE(HDR_P(prev_bp)) + GET_BLOCK_SIZE(HDR_P(next_bp));

        PUT(HDR_P(prev_bp), MAKE_H_F(size, 0));
        PUT(FTR_P(next_bp), MAKE_H_F(size, 0));
        bp = prev_bp;
    }
    return bp;
}



// 가용 블럭 찾는 코드 -> 완
static void* first_fit(size_t size) {
    int idx = get_list_index(size);

    while(idx < LIST_LIMIT) {
        void* bp = free_list_head[idx].head;

        while(bp != NULL) {
            if(size <= GET_BLOCK_SIZE(HDR_P(bp))) {
                return bp;
            }
            bp = (void*)GET(SUCC_P(bp));
        }
        idx++;
    }
    return NULL;
}



static void place(void *bp, size_t a_size) {
    size_t c_size = GET_BLOCK_SIZE(HDR_P(bp));

    // split하면 자동으로 할당 블럭 만들어줌 나중에 매크로 함수로 바꾸면 성능 향상될 거 같음
    remove_free_list(bp);


    // a_size 할당 받을 블럭 크기, c_size 블럭 전체 크기, c_size - a_size 남은 블럭 크기
    // split 가능하면 하고 가능하지 않으면 그대로 할당
    // 남은 크기가 32보다 클 경우 (최소 블럭 크기 = 8+8+8+8) 헤더, 포인터2개, 풋터 
    if((c_size - a_size) >= (2*DW_SIZE)) {
        INSERT_H(bp, a_size, 1);
        INSERT_F(bp, a_size, 1);

        // 분리된 공간 가용 영역으로 만들기
        bp = NEXT_BLOCK_P(bp);
        INSERT_H(bp, c_size - a_size, 0);
        INSERT_F(bp, c_size - a_size, 0);
        insert_free_list(bp);
    }
    else {
        INSERT_H(bp, c_size, 1);
        INSERT_F(bp, c_size, 1);
    }
}



// 경우의 수 2가지
// 1. head가 존재하지 않을 경우
// 2. head가 존재할 경우
static void* insert_free_list(void* bp) {
    size_t size = GET_BLOCK_SIZE(HDR_P(bp));
    int idx = get_list_index(size);
    void* head = free_list_head[idx].head;

    PUT(PRED_P(bp), NULL);
    PUT(SUCC_P(bp), head);

    if(head != NULL) {
        PUT(PRED_P(head), bp);
    }
    free_list_head[idx].head = bp;
    return bp;
}


