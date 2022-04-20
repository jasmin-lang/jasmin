require import List Int IntDiv CoreMap.
from Jasmin require import JModel.
require import Leakage_models.
require Keccak1600_scalar_BL_CL32.
import StdOrder.IntOrder Ring.IntID.

clone import Keccak1600_scalar_BL_CL32.T with
theory LeakageModel <-  LeakageModelCL32.


require import Array5 Array25.
require import WArray40 WArray200.

equiv ct: 
  M.__keccak1600_scalar ~ M.__keccak1600_scalar :
     ={inlen,s_outlen,M.leakages,rate,in_0,s_out,iotas} ==> ={M.leakages}.
proc.

(* Squeeze *)
call(_: ={outlen, s_out, M.leakages,iotas,rate} ==> ={M.leakages}).

proc.
wp;call(_: ={outlen, out,M.leakages} ==> ={M.leakages}).
proc.
by sim.
wp;call(_: ={M.leakages,arg} ==> ={M.leakages,res}). 
proc.
by sim.

(* Squeeze last f *)
wp;call(_: ={M.leakages,iotas} ==> ={M.leakages}  /\ res{1}.`2 = res{2}.`2). 
proc.

wp;while (={zf,iotas,M.leakages}).

(* Squeeze last f loop round2x 2 *)
wp;call(_: ={M.leakages,iotas,o} ==> ={M.leakages}). 
proc.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages} ==> ={M.leakages}). 
proc.
by sim.
by auto => />.

(* Squeeze   last f last f loop round2x 1 *)
wp;call(_: ={M.leakages,iotas,o} ==> ={M.leakages}). 
proc.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages} ==> ={M.leakages}). 
proc.
by sim.
by auto => />.

by auto => />.


(* Squeeze  last f last f first round2x 2 *)
wp;call(_: ={M.leakages,iotas,o} ==> ={M.leakages}). 
proc.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages} ==> ={M.leakages}). 
proc.
by sim.
by auto => />.

(* Squeeze  last f first round2x 1 *)
wp;call(_: ={M.leakages,iotas,o} ==> ={M.leakages}). 
proc.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.

wp;call(_: ={M.leakages} ==> ={M.leakages}). 
proc.
by sim.

wp;call(_: ={M.leakages} ==> ={M.leakages}). 
proc.
by sim.

by auto => />.

by auto => />.

wp;while (={rate,s_out,outlen,iotas,M.leakages}); last by auto => />. 

wp;call(_: ={outlen, out,rate,M.leakages} ==> ={M.leakages,res}).
proc.
by sim.
wp;call(_: ={M.leakages,arg} ==> ={M.leakages,res}). 
proc.
by sim.

(* Squeeze first f *)
wp;call(_: ={M.leakages,iotas} ==> ={M.leakages}  /\ res{1}.`2 = res{2}.`2). 
proc.

wp;while (={zf,iotas,M.leakages}).

(* Squeeze first f loop round2x 2 *)
wp;call(_: ={M.leakages,iotas,o} ==> ={M.leakages}). 
proc.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages} ==> ={M.leakages}). 
proc.
by sim.
by auto => />.

(* Squeeze  first f last f loop round2x 1 *)
wp;call(_: ={M.leakages,iotas,o} ==> ={M.leakages}). 
proc.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages} ==> ={M.leakages}). 
proc.
by sim.
by auto => />.

by auto => />.


(* Squeeze  last f last f first round2x 2 *)
wp;call(_: ={M.leakages,iotas,o} ==> ={M.leakages}). 
proc.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages} ==> ={M.leakages}). 
proc.
by sim.
by auto => />.

(* Squeeze  last f first round2x 1 *)
wp;call(_: ={M.leakages,iotas,o} ==> ={M.leakages}). 
proc.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.

wp;call(_: ={M.leakages} ==> ={M.leakages}). 
proc.
by sim.

wp;call(_: ={M.leakages} ==> ={M.leakages}). 
proc.
by sim.

by auto => />.

by auto => />.

wp;call(_: ={M.leakages,arg} ==> ={M.leakages,res}). 
proc.
by sim.

by auto => />.

(* Initialization *)

wp;call(_: ={M.leakages,iotas,rate,in_0,inlen} ==> ={M.leakages} /\ res{1}.`2 = res{2}.`2 /\ res{1}.`3 = res{2}.`3); last by inline *;wp; while (={i,M.leakages}) => //=; auto => />.

(* Absorb *)
proc.
wp;call(_: ={M.leakages,rate,in_0,inlen} ==> ={M.leakages}).
proc.
by sim.
wp;while (={rate,inlen,in_0,iotas,M.leakages}).
wp;call(_: ={M.leakages,arg} ==> ={M.leakages,res}).
proc.
by sim.

(* Absorb f *)
wp;call(_: ={M.leakages,iotas} ==> ={M.leakages}  /\ res{1}.`2 = res{2}.`2). 
proc.

auto => />.
progress.

wp;while (={zf,iotas,M.leakages}).

(* Absorb f  loop round2x 2 *)
wp;call(_: ={M.leakages,iotas,o} ==> ={M.leakages}). 
proc.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages} ==> ={M.leakages}). 
proc.
by sim.
by auto => />.

(* Absorb f  loop round2x 1 *)
wp;call(_: ={M.leakages,iotas,o} ==> ={M.leakages}). 
proc.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages} ==> ={M.leakages}). 
proc.
by sim.
by auto => />.

by auto => />.


(* Absorb f  first round2x 2 *)
wp;call(_: ={M.leakages,iotas,o} ==> ={M.leakages}). 
proc.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages} ==> ={M.leakages}). 
proc.
by sim.
by auto => />.

(* Absorb f first round2x 1 *)
wp;call(_: ={M.leakages,iotas,o} ==> ={M.leakages}). 
proc.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages,row} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages,offset} ==> ={M.leakages}). 
proc.
while (={j,M.leakages,offset}). 
by inline *; sim.
by auto => />.
wp;call(_: ={M.leakages} ==> ={M.leakages}). 
proc.
by sim.
wp;call(_: ={M.leakages} ==> ={M.leakages}). 
proc.
by sim.
by auto => />.

by auto => />.


wp;call(_: ={M.leakages,arg} ==> ={M.leakages,res}). 
proc.
by sim.


wp;call(_: ={M.leakages,in_0,inlen,rate} ==> ={M.leakages}  /\ res{1}.`2 = res{2}.`2 /\ res{1}.`3 = res{2}.`3). 
proc.
wp;while(={i,rate64,M.leakages,in_0}).
by sim.
by auto => />.

by auto => />.
 
by auto => />.

qed.
