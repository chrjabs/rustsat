capi: capi.cpp
	g++ -I.. -c capi.cpp -o capi.o
	g++ capi.o ../../target/release/librustsat.a -o capi.out

capi-ipasir: capi-ipasir.cpp
	g++ -I.. -I${IPASIR_INC} -c capi-ipasir.cpp -o capi-ipasir.o
	g++ capi-ipasir.o ../../target/release/librustsat.a ${IPASIR_LIB} -o capi-ipasir.out
