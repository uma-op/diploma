# syj201 Comparison: Current Prover vs intuitR

Chart: `benchmarks/syj201/syj201-comparison.svg`

| N | current result | current total ms | intuitR result | intuitR reported total ms | intuitR wall ms |
| ---: | --- | ---: | --- | ---: | ---: |
| 1 | valid | 16.653 | valid | 0.000 | 12.360 |
| 2 | valid | 54.656 | valid | 1.000 | 12.287 |
| 3 | valid | 186.362 | valid | 1.000 | 12.236 |
| 4 | valid | 603.223 | valid | 1.000 | 12.948 |
| 5 | valid | 1338.659 | valid | 2.000 | 12.784 |
| 6 | valid | 13113.380 | valid | 3.000 | 12.670 |
| 7 | valid | 19778.133 | valid | 5.000 | 12.122 |
| 8 | valid | 46433.652 | valid | 4.000 | 12.676 |
| 9 | valid | 179726.950 | valid | 8.000 | 22.046 |
| 10 | valid | 976911.016 | valid | 6.000 | 12.587 |

Both provers solve all `N=1..10` instances. The current prover time grows from ~17 ms (N=1) to ~977 s (N=10); intuitR stays in the low millisecond range by internal timers.
