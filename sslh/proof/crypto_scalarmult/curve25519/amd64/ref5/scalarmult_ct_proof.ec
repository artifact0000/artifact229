require import Scalarmult_ct.

equiv jade_scalarmult_curve25519_amd64_ref5 : 
  M.jade_scalarmult_curve25519_amd64_ref5 ~ M.jade_scalarmult_curve25519_amd64_ref5 :
    ={rp, kp, up, M.leakages} ==> ={M.leakages}.
proof.
proc; inline *; sim => />.
qed.

