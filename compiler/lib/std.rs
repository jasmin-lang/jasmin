// ** License
// -----------------------------------------------------------------------
// Copyright 2016--2017 IMDEA Software Institute
// Copyright 2016--2017 Inria
//
// Permission is hereby granted, free of charge, to any person obtaining
// a copy of this software and associated documentation files (the
// "Software"), to deal in the Software without restriction, including
// without limitation the rights to use, copy, modify, merge, publish,
// distribute, sublicense, and/or sell copies of the Software, and to
// permit persons to whom the Software is furnished to do so, subject to
// the following conditions:
//
// The above copyright notice and this permission notice shall be
// included in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
// IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
// CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
// TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
// SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
// -----------------------------------------------------------------------

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
