pub fn bash_stub(state: &mut [u8; 192]) {
    unsafe { jlib_sys::bashF0_stub(state.as_mut_ptr()) }
}

pub fn bash(state: &mut [u8; 192]) {
    unsafe { jlib_sys::bashF0(state.as_mut_ptr()) }
}

pub fn bash_avx2(state: &mut [u8; 192]) {
    unsafe { jlib_sys::bashF0_avx2(state.as_mut_ptr()) }
}

pub fn blake2b_stub(hash: &mut [u8; 64], perso: &[u8; 16], data: &[u8]) {
    let length: u64 = data.len() as u64;
    unsafe {
        jlib_sys::blake2b_stub(
            hash.as_mut_ptr(),
            64u64,
            perso.as_ptr(),
            data.as_ptr(),
            length,
        )
    }
}

pub fn blake2b(hash: &mut [u8; 64], perso: &[u8; 16], data: &[u8]) {
    let length: u64 = data.len() as u64;
    unsafe {
        jlib_sys::blake2b(
            hash.as_mut_ptr(),
            64u64,
            perso.as_ptr(),
            data.as_ptr(),
            length,
        )
    }
}

pub fn gimli_stub(state: &mut [u8; 48]) {
    unsafe { jlib_sys::gimli_stub(state.as_mut_ptr()) }
}

pub fn gimli(state: &mut [u8; 48]) {
    unsafe { jlib_sys::gimli(state.as_mut_ptr()) }
}

pub fn gimli_avx2(state: &mut [u8; 48]) {
    unsafe { jlib_sys::gimli_avx2(state.as_mut_ptr()) }
}

pub fn poly1305_stub(out: &mut [u8], plain: &[u8], key: &[u8; 32]) {
    let length: u64 = plain.len() as u64;
    unsafe { jlib_sys::poly1305_stub(out.as_mut_ptr(), plain.as_ptr(), length, key.as_ptr()) }
}

pub fn poly1305(out: &mut [u8], plain: &[u8], key: &[u8; 32]) {
    let length: u64 = plain.len() as u64;
    unsafe { jlib_sys::poly1305_ref3(out.as_mut_ptr(), plain.as_ptr(), length, key.as_ptr()) }
}

pub fn poly1305_avx2(out: &mut [u8], plain: &[u8], key: &[u8; 32]) {
    let length: u64 = plain.len() as u64;
    unsafe { jlib_sys::poly1305_avx2(out.as_mut_ptr(), plain.as_ptr(), length, key.as_ptr()) }
}

pub fn xxh_stub(plain: &[u8], seed: u64) -> u64 {
    let length: u64 = plain.len() as u64;
    unsafe { jlib_sys::xxhash_stub(plain.as_ptr(), length, seed) }
}

pub fn xxh(plain: &[u8], seed: u64) -> u64 {
    let length: u64 = plain.len() as u64;
    unsafe { jlib_sys::xxhash(plain.as_ptr(), length, seed) }
}
