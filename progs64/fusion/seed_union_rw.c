/* seed_union_rw.c — union 视窗转换 × 指针 cast 的验证矩阵被测程序
 * A: 直接视窗转换（union 成员视图混合）
 * B: 指针 + 显式类型转换（*(T*)s 别名访问）
 * C: 同尺寸对照（官方 union hack 白名单内的形态）
 * 回归证明见本目录的 verif_fusion.v。 */

typedef unsigned int u32;
typedef unsigned long long u64;

union seed {
    u32 v32;
    u64 v64;
};

union twin32 {
    u32 a;
    u32 b;
};

union f_or_i {
    float f;
    u32 i;
};

/* ---- A. 直接视窗转换 ---- */

u32 rw32(union seed *s, u32 x)   /* A1 基线：同字段往返 */
{
    s->v32 = x;
    return s->v32;
}

u64 rw64(union seed *s, u64 c)   /* A2 基线：同字段往返 */
{
    s->v64 = c;
    return s->v64;
}

u32 w64_r32(union seed *s, u64 c) /* A3 撞墙候选：宽写窄读 */
{
    s->v64 = c;
    return s->v32;
}

u64 w64_w32_r64(union seed *s, u64 c, u32 x) /* A4 撞墙候选：宽写窄写宽读 */
{
    s->v64 = c;
    s->v32 = x;
    return s->v64;
}

/* ---- B. 指针 + 显式类型转换 ---- */

u64 ptr_r64_after_w64(union seed *s, u64 c) /* B1：v64 写（占满8字节）后 u64 cast 读 */
{
    s->v64 = c;
    return *(u64 *)s;
}

u32 ptr_r32_after_w32(union seed *s, u32 x) /* B2：v32 写后 u32 cast 读（TT 吸收 spacer） */
{
    s->v32 = x;
    return *(u32 *)s;
}

u64 ptr_r64_after_w32(union seed *s, u32 x) /* B3 撞墙候选：v32 写后跨 spacer 宽读 */
{
    s->v32 = x;
    return *(u64 *)s;
}

u64 ptr_ptr_mix(u64 *w, u32 x) /* B4 撞墙候选：窄 cast 写 + 宽读 */
{
    *(u32 *)w = x;
    return *w;
}

u64 ptr_only(u64 *w, u32 x) /* B5 正例：单一视图 + 值转换（非 punning） */
{
    *w = x;
    return *w;
}

/* ---- D. 读优先交错路径（读-改-写场景） ---- */

u32 w0_r32(union seed *s) /* A3'：写0读0 最简形态（w64_r32 的 c=0 特例） */
{
    s->v64 = 0;
    return s->v32;
}

u64 r32_r64_w64(union seed *s, u32 newlo) /* D1：读u32 → 读u64 → 写u64。
 * 真实语义（s->v64 初值 c）：old = c 低 32 位，cur = c，
 * 返回 (c & ~0xFFFFFFFF) | newlo —— 完全确定；
 * VST 侧：读 u32 发生在 v64 活跃视角（跨视图读），预期撞墙 */
{
    u32 old = s->v32;
    u64 cur = s->v64;
    u64 res = cur - old + newlo;
    s->v64 = res;
    return res;
}

/* ---- C. 同尺寸对照 ---- */

u32 cross32(union twin32 *u, u32 x) /* C4：同尺寸整型跨成员（Mint32→Mint32 白名单内） */
{
    u->a = x;
    return u->b;
}

u32 f2i(float x) /* C3：官方 fabs_single 同款（Mfloat32→Mint32 白名单内） */
{
    union f_or_i u;
    u.f = x;
    return u.i;
}
