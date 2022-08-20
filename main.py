from trenc import TRENC
from beleniosrf import BELENIOSRF
from charm.toolbox.pairinggroup import PairingGroup

group = PairingGroup("MNT159")
assert group.InitBenchmark(), "failed to initialize benchmark"

n_run = 100

# BELENIOS RF
print("BeleniosRF")
for k in [1, 2, 4, 8, 32]:
    s = BELENIOSRF(group, k)
    pk, sk = s.keygen()
    m = [i%2 for i in range(k)]
    group.StartBenchmark(["CpuTime"])
    for i in range(n_run):
        s.encrypt(pk, m)
    group.EndBenchmark()

    print(k)
    msmtDict = group.GetGeneralBenchmarks()
    print("<=== General Benchmarks ===>")
    print("Cpu time := ", msmtDict["CpuTime"]/n_run)

# TRENC
print("TRENC group element")
for k in [1, 2, 4, 8, 32]:
    s = TRENC(group, 1)
    pk, sk = s.keygen(bit_by_bit = False)
    m = [int("".join([str(i%2) for i in range(k)]), 2)]
    group.StartBenchmark(["CpuTime"])
    for i in range(n_run):
        s.encrypt(pk, m, bit_by_bit = False)
    group.EndBenchmark()

    print(k)
    msmtDict = group.GetGeneralBenchmarks()
    print("<=== General Benchmarks ===>")
    print("Cpu time := ", msmtDict["CpuTime"]/n_run)


# TRENC bit-by-bit
print("TRENC bit-by-bit")
for k in [1, 2, 4, 8, 32]:
    s = TRENC(group, k)
    pk, sk = s.keygen(bit_by_bit = True)
    m = [i%2 for i in range(k)]
    group.StartBenchmark(["CpuTime"])
    for i in range(n_run):
        s.encrypt(pk, m, bit_by_bit = True)
    group.EndBenchmark()

    print(k)
    msmtDict = group.GetGeneralBenchmarks()
    print("<=== General Benchmarks ===>")
    print("Cpu time := ", msmtDict["CpuTime"]/n_run)
