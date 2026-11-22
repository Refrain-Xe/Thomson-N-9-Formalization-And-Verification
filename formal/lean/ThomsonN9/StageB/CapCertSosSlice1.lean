import ThomsonN9.StageB.CapCertSosData

set_option maxHeartbeats 16000000
set_option maxRecDepth 200000

namespace ThomsonN9.StageB.CapCertSosSlice1

open ThomsonN9.StageB.CapCertSosData

theorem kron_t_1 : checkKronCapAtT (wForT 1) 1 = true := by decide +kernel

end ThomsonN9.StageB.CapCertSosSlice1
