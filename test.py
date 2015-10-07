from decimal import *
getcontext().prec=120
a_float = 33.0
b_float = 1.0 / 1243313.0
a = Decimal(a_float)
b = Decimal(b_float)
s_float = a_float + b_float
s = a + b
t = s - Decimal(s_float)