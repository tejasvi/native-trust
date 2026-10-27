import BVS.Driver4
set_option bvs4.workdir "/home/ntbuild/work_bvscale/satwork"
set_option bvs4.log "/home/ntbuild/work_bvscale/logs/DC_w16.progress"
set_option maxHeartbeats 0

theorem mul_three (x : BitVec 16) : x * 3 = x + x + x := by bv_decide

bvs4_kernelize mul_three
#print axioms mul_three.bvs4
