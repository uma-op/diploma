# syj201 Comparison: Current Prover vs intuitR

Generated TPTP formulas for `intuitR` are stored in `benchmarks/syj201/intuitr-formulas`. Full logs are in `benchmarks/syj201/intuitr-logs`.

CSV files:

- `benchmarks/syj201/syj201-n1-10.csv`
- `benchmarks/syj201/intuitr-syj201-n1-10.csv`
- `benchmarks/syj201/syj201-comparison.csv`

Chart: `benchmarks/syj201/syj201-comparison.svg`.

| N | current result | current total ms | intuitR result | intuitR reported total ms | intuitR wall ms |
| ---: | --- | ---: | --- | ---: | ---: |
| 1 | valid | 36.473 | valid | 0.000 | 12.360 |
| 2 | valid | 642.408 | valid | 1.000 | 12.287 |
| 3 | valid | 10005.497 | valid | 1.000 | 12.236 |
| 4 | timeout | 300000.000 | valid | 1.000 | 12.948 |
| 5 | timeout | 300000.000 | valid | 2.000 | 12.784 |
| 6 | timeout | 300000.000 | valid | 3.000 | 12.670 |
| 7 | timeout | 300000.000 | valid | 5.000 | 12.122 |
| 8 | timeout | 300000.000 | valid | 4.000 | 12.676 |
| 9 | timeout | 300000.000 | valid | 8.000 | 22.046 |
| 10 | timeout | 300000.000 | valid | 6.000 | 12.587 |

`intuitR` solves all generated `N=1..10` instances. The current prover solves `N=1..3` within the 300 second limit; `N=4..10` timed out.
