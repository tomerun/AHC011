OBJ = main.o
TARGET = main
# COMPILEOPT = -Wall -Wextra -Wshadow -Wno-sign-compare -std=gnu++17 -O2 -DLOCAL -D_GLIBCXX_DEBUG -g
COMPILEOPT = -Wall -Wextra -Wshadow -Wno-sign-compare -std=gnu++17 -O2 -DLOCAL
vpath %.cpp ..
vpath %.h ..

.PHONY: all clean

all: $(TARGET)

$(TARGET): $(OBJ)
	g++-10 -o $@ $(OBJ)

%.o: %.cpp main.cpp
	g++-10 $(COMPILEOPT) -c $<

clean:
	rm -f $(TARGET)
	rm -f $(OBJ)
