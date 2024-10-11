COQBIN=
SL_DIR=

-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

COQ_FLAG= \
  -R $(SL_DIR)SeparationLogic SimpleC.SL \
  -R $(SL_DIR)unifysl Logic \
  -R $(SL_DIR)Asrtdef SimpleC.ASRT \
  -R $(SL_DIR)AuxiFun SimpleC.ASRTFUN \
  -R $(SL_DIR)Cdef SimpleC.CSE \
  -R $(SL_DIR)sets SetsClass \
  -R $(SL_DIR)compcert_lib compcert.lib \
  -R $(SL_DIR)auxlibs AUXLib \
  -R $(SL_DIR)test SimpleC.PT \
  -R $(SL_DIR)examples SimpleC.EE \
  -R $(SL_DIR)StrategyLib SimpleC.StrategyLib \
  -R $(SL_DIR)MonadLib StateMonad \
  -R $(SL_DIR)MonadLib/monadnrm StateMonad.monadnrm \
  -R $(SL_DIR)MonadLib/monaderror StateMonad.monaderror \
  -R $(SL_DIR)Common SimpleC.Common \
  -R $(SL_DIR)CoreLang SimpleC.CoreLang \
  -R $(SL_DIR)Frontend SimpleC.Frontend \
  -R . Example

COQ_FILES=$(wildcard ./*.v)

$(COQ_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_FLAG) $*.v

_CoqProject:
	@echo $(COQ_FLAG) > _CoqProject

depend:
	$(COQDEP) $(COQ_FLAG) $(COQ_FILES) > .depend

all: _CoqProject depend goal_check.vo

clean:
	@$(RM) .depend
	@$(RM) .lia.cache
	@$(RM) .nia.cache
	@$(RM) _CoqProject
	@$(RM) *.aux
	@$(RM) *.glob
	@$(RM) *.vo
	@$(RM) *.vok
	@$(RM) *.vos

.PHONY: all clean depend
.DEFAULT_GOAL=all

-include .depend
