from random import randint as rnd, choice, seed
from sys import argv
seed(' '.join(argv))

n = int(argv[1])
mx = int(argv[2])
A = [[rnd(0, mx) for j in range(n)] for i in range(n)]
for i in range(n):
    A[i][i] = 0
    for j in range(i):
        A[i][j] = A[j][i]
print n
for a in A:
    print ' '.join(map(str, a))
