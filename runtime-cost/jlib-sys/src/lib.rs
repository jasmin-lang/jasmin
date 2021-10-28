#[link(name = "jlib", kind = "static")]
extern "C" {
    // Bash: in place permutation of [u8; 192]
    pub fn bashF0_stub(state: *mut u8);
    pub fn bashF0(state: *mut u8);
    pub fn bashF0_avx2(state: *mut u8);
    // Blake2b hashlen ≤ 64
    pub fn blake2b(
        hash: *mut u8, // [u8; hashlen]
        hashlen: u64,
        perso: *const u8, // [u64; 2]
        data: *const u8,
        length: u64,
    );
    pub fn blake2b_stub(
        hash: *mut u8, // [u8; hashlen]
        hashlen: u64,
        perso: *const u8, // [u64; 2]
        data: *const u8,
        length: u64,
    );
    pub fn chacha20_stub(
        output: *mut u8,
        plain: *const u8,
        len: u32,
        key: *const u8,   // [u128; 2]
        nonce: *const u8, // [u32; 2]
        counter: u32,
    );
    pub fn chacha20_ref(
        output: *mut u8,
        plain: *const u8,
        len: u32,
        key: *const u8,   // [u128; 2]
        nonce: *const u8, // [u32; 2]
        counter: u32,
    );
    // Gimli: in place permutation of [u8; 48]
    pub fn gimli_stub(state: *mut u8);
    pub fn gimli(state: *mut u8);
    pub fn gimli_avx2(state: *mut u8);

    pub fn poly1305_stub(
        out: *mut u8,     // 16 bytes
        plain: *const u8, // len bytes
        len: u64,
        key: *const u8, // 32 bytes, r followed by s
    );
    pub fn poly1305_ref3(
        out: *mut u8,     // 16 bytes
        plain: *const u8, // len bytes
        len: u64,
        key: *const u8, // 32 bytes, r followed by s
    );
    pub fn poly1305_avx2(
        out: *mut u8,     // 16 bytes
        plain: *const u8, // len bytes
        len: u64,
        key: *const u8, // 32 bytes, r followed by s
    );

    pub fn xxhash_stub(data: *const u8, len: u64, seed: u64) -> u64;
    pub fn xxhash(data: *const u8, len: u64, seed: u64) -> u64;

}
