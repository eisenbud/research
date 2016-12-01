-- M<--  S<-- m S(-d) <-- n S(-d-1) <-- \sum_{n-m+1} S(-d-1-x_i)
--2* (const term of hil poly H_M(t)) is
restart
S=kk[t,m, n, x_1, x_2, d]
f=(t+2)*(t+1)-m*(t-d+2)*(t-d+1)+n*(t-d+1)*(t-d)-(t-d+1-x_1)*(t-d-x_1)-(t-d+1-x_2)*(t-d-x_2)
substitute(f, {m=>1+d+x_1+x_2})

