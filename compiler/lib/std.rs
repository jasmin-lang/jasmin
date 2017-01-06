// we use stack! for all types because the storage is required, but it is ignored

decl! { fn add    (x: stack! (b64), y: stack! (b64))                  -> stack! (b64);                }
decl! { fn add_cf (x: stack! (b64), y: stack! (b64))                  -> (stack! (b1), stack! (b64)); }
decl! { fn adc    (x: stack! (b64), y: stack! (b64), cf: stack! (b1)) -> stack! (b64);                }
decl! { fn adc_cf (x: stack! (b64), y: stack! (b64), cf: stack! (b1)) -> (stack! (b1),stack! (b64));  }
decl! { fn sub    (x: stack! (b64), y: stack! (b64))                  -> stack! (b64);                }
decl! { fn sub_cf (x: stack! (b64), y: stack! (b64))                  -> (stack! (b1),stack! (b64));  }
decl! { fn sbb    (x: stack! (b64), y: stack! (b64), cf: stack! (b1)) -> stack! (b64);                }
decl! { fn sbb_cf (x: stack! (b64), y: stack! (b64), cf: stack! (b1)) -> (stack! (b1),stack! (b64));  }
decl! { fn mul    (x: stack! (b64), y: stack! (b64))                  -> (stack! (b64),stack! (b64)); }
decl! { fn imul   (x: stack! (b64), y: stack! (b64))                  -> stack! (b64);                }
decl! { fn xor    (x: stack! (b64), y: stack! (b64))                  -> stack! (b64);                }
decl! { fn band   (x: stack! (b64), y: stack! (b64))                  -> stack! (b64);                }
decl! { fn bor    (x: stack! (b64), y: stack! (b64))                  -> stack! (b64);                }
decl! { fn shr    (x: stack! (b64), y: stack! (b64))                  -> stack! (b64);                }
decl! { fn shl    (x: stack! (b64), y: stack! (b64))                  -> stack! (b64);                }
