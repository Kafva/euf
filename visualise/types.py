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

    @classmethod
    def new(cls, items:list):
        assert len(items) == 13
        return cls(
            func_name = items[0],
            identity = items[1] == "True",
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


