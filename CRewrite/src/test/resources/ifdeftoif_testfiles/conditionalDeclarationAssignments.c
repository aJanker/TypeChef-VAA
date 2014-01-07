int a = 5 *
#if definedEx(A)
0
#else
1
#endif
;
void main() {
	int x = 5 *
	#if definedEx(A)
0
#else
1
#endif
;
	int y = 5 *
#if definedEx(A)
(0 * a)
#else
(1 * a)
#endif
;
	int z = 5 *
#if definedEx(B)
(0 * a)
#else
(1 * a)
#endif
;
}