typedef unsigned int u32;
typedef unsigned long long u64;

union cell_a { u32 low; u64 wide; };
union cell_b { u64 wide; u32 low; };
struct record_with_frame { u32 tag; union cell_b payload; };

union cell_a first;
union cell_b second;
struct record_with_frame framed;

u32 store_a(union cell_a *p, u64 x) { p->wide = x; return p->low; }
u32 store_b(union cell_b *p, u64 x) { p->wide = x; return p->low; }
