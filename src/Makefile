CXX = g++
CFLAGS = -Wall -g -static -std=c++11 -O3

OBJS = scanner.o parser.o ast.o cnf.o skeleton.o

all: YicesLS

YicesLS: $(OBJS) boolidl.hpp
	$(CXX) $(CFLAGS) $(OBJS) boolidl.cpp -o $@


scanner.o: scanner.cc parser.h ast.h
	$(CXX) $(CFLAGS) -c scanner.cc -o $@


parser.o: parser.cc parser.h ast.h
	$(CXX) $(CFLAGS) -c parser.cc -o $@

ast.o: ast.cc ast.h parser.h
	$(CXX) $(CFLAGS) -c ast.cc -o $@

cnf.o: cnf.cc cnf.h ast.h parser.h
	$(CXX) $(CFLAGS) -c cnf.cc -o $@

skeleton.o: skeleton.cc skeleton.h cnf.o parser.h
	$(CXX) $(CFLAGS) -c skeleton.cc -o $@
 
clean:
	-rm $(OBJS)

.PONEY:
	all
	clean
