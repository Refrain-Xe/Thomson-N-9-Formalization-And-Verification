import ThomsonN9.StageB.CapCertSosData

set_option maxHeartbeats 16000000
set_option maxRecDepth 200000

namespace ThomsonN9.StageB.CapCertSosSlice7

open ThomsonN9.StageB.CapCertSosData

theorem kron_t_7 : checkKronCapAtT (wForT 7) 7 = true := by decide +kernel

end ThomsonN9.StageB.CapCertSosSlice7
