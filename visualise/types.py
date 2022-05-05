import re
from dataclasses import dataclass, field
from datetime import datetime
from src.config import CONFIG
from src.types import AnalysisResult, IdentifierLocation

@dataclass(init=True)
class CbmcResult:
    func_name:str
    identity:bool
    result: AnalysisResult
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

        return cls(
            func_name = items[0],
            identity = False if items[1] == "False" else True,
            result = AnalysisResult[items[2]],
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
    A list of all the analysis results recorded for a perticular
    function. By using a list with duplicate entries we can
    see the distrubtion of results and fetch a set()
    '''
    func_name: str
    results: list[AnalysisResult]    = field(default_factory=list)
    results_id: list[AnalysisResult] = field(default_factory=list)

    def pretty(self,ident:bool=False) -> str:
        out = f"{self.func_name}: [\n"
        res = self.results_id if ident else self.results
        for r in set(res):
            cnt = res.count(r)
            out += f"{CONFIG.INDENT}{r.name} ({cnt}),\n"
        return out.strip(",\n")+"\n]"

    def pretty_md(self,ident:bool=False) -> str:
        out = f"## `{self.func_name}()`\n```\n[\n"
        res = self.results_id if ident else self.results
        for r in set(res):
            cnt = res.count(r)
            out += f"{CONFIG.INDENT}{r.name} ({cnt}),\n"
        return out.strip(",\n")+"\n]\n```\n"

