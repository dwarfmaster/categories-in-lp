
OBJS=Test.vo

.PHONY:all
all: $(OBJS)

%.vo: %.v
	coqc -noinit -indices-matter $^

.PHONY:clean
clean:
	rm -f *.vo *.vok *.vos *.glob
