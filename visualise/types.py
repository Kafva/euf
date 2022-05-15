import re
from dataclasses import dataclass, field
from datetime import datetime

from src.types import AnalysisResult, HarnessType, IdentifierLocation
from src.util import flatten

@dataclass(init=True)
class CbmcResult:
    func_name:str
    harness_type: HarnessType
    result: set[AnalysisResult]
    runtime: datetime
    driver: str
    location_old: IdentifierLocation
    location_new: IdentifierLocation
    commit_old: str
    commit_new: str

    @classmethod
    def new(cls, items:list, directory:str):
        assert len(items) == 13

        commit_old = re.search(r"_[a-z0-9]{4}_", directory).\
                group(0)[1:-1] # type: ignore
        commit_new = re.search(r"_[a-z0-9]{4}$", directory).\
                group(0)[1:] # type: ignore

        # The result field can hold more than one value (',' separated)
        # if the HarnessType is NONE.
        result = { AnalysisResult[r] for r in items[2].split(',') }

        return cls(
            func_name = items[0],
            # pylint: disable=simplifiable-if-expression
            harness_type = HarnessType[items[1]],
            result = result,
            runtime = datetime.now(),
            driver = items[4],
            location_old = IdentifierLocation(
                _filepath = items[5],
                line = items[6],
                column = items[7],
                name = items[8].strip()
            ),
            location_new = IdentifierLocation(
                _filepath = items[9],
                line = items[10],
                column = items[11],
                name = items[12].strip()
            ),
            commit_old = commit_old,
            commit_new = commit_new
        )

@dataclass(init=True)
class FunctionResult:
    '''
    A list of all the analysis results recorded for a particular
    function. By using a list with duplicate entries we can
    see the distribution of results and fetch a set()
    '''
    func_name: str

    # Maintain a list of each Cbmc result attained for this
    # function. This allows us to retroactively find out
    # which commits yielded a specific result
    #
    # If we ever need  a complete list of all CbmcResults
    # we can derive that from our list of function results
    cbmc_results: list[CbmcResult] = field(default_factory=list)

    def _result_in_predicate(self, predicates:set[HarnessType]) -> list[AnalysisResult]:
        res = filter(lambda c:
            c.harness_type in predicates,
            self.cbmc_results
        )
        # A Cbmc result can contain more than one result if the HarnessType
        # is set to NONE.
        return flatten([ list(c.result) for c in res ])

    def results(self) -> list[AnalysisResult]:
        ''' Results from STANDARD harness verification '''
        return self._result_in_predicate({HarnessType.STANDARD})

    def results_id(self) -> list[AnalysisResult]:
        ''' Results from IDENTITY and IDENTITY_OLD harness verification '''
        return self._result_in_predicate({
            HarnessType.IDENTITY, HarnessType.IDENTITY_OLD
        })

    def results_none(self) -> list[AnalysisResult]:
        ''' Results derived from a failed precondition check '''
        return self._result_in_predicate({HarnessType.NONE})

    def has_multi_result(self,identity:bool=False):
        '''
        Considers a different set of results as "successful" based on 
        the current CONFIG object
        '''
        res = self.results_id() if identity else self.results()
        return any(r in AnalysisResult.results_that_reduce()
                for r in res
            ) and \
            (AnalysisResult.FAILURE in res or
             AnalysisResult.FAILURE_UNWIND_FAIL in res)

    def pretty(self,identity:bool=False,only_multi:bool=False) -> str:
        '''
        Highlight if both SUCCESS and FAILURE was recorded
        for a function, these cases are most interesting since
        they enable a comparison between a (according to EUF)
        equivalent and influential update to the same function
        '''
        res = self.results_id() if identity else self.results()
        if self.has_multi_result(identity):
            out = f"\033[32;4m{self.func_name}\033[0m: [\n"
        else:
            if only_multi:
                return ""
            out = f"{self.func_name}: [\n"

        for r in set(res):
            cnt = res.count(r)
            out += f"  {r.name} ({cnt}),\n"
        return out.strip(",\n")+"\n]"

    def pretty_md(self,identity:bool=False) -> str:
        out = f"## `{self.func_name}()`\n"
        res = self.results_id() if identity else self.results()
        for r in set(res):
            cnt = res.count(r)
            out += f"> {r.name} ({cnt})\n"
        return out

