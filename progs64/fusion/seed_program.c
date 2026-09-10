typedef unsigned int u32;
typedef unsigned long long u64;

union seed {
    u32 v32;
    u64 v64;
};

union seed global_seed = { .v64 = 0 };

u32 w64_r32(union seed *s, u64 c)
{
    s->v64 = c;
    return s->v32;
}

u32 mixed_caller(union seed *s, u64 c)
{
    u32 result = w64_r32(s, c);
    return result;
}

int main(void)
{
    u32 result = mixed_caller(&global_seed, 0x10000002aULL);
    return (int)result;
}
