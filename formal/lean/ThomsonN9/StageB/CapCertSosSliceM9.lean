import ThomsonN9.StageB.CapCertSosData

set_option maxHeartbeats 16000000
set_option maxRecDepth 200000

namespace ThomsonN9.StageB.CapCertSosSliceM9

open ThomsonN9.StageB.CapCertSosData

theorem kron_t_m9 : checkKronCapAtT (wForT (-9 : ℤ)) (-9 : ℤ) = true := by decide +kernel

end ThomsonN9.StageB.CapCertSosSliceM9
