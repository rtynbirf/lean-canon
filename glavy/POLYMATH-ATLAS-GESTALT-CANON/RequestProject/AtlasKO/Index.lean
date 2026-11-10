/-
# ATLAS Knowledge Objects — оглавление слоя

Формализация первичного корпуса документов Атласа
(`docs/atlas/ATLAS-*.md`): семнадцать объектов знания типов STEP, CONCEPT,
INVARIANT и MECHANISM.

| модуль | содержание |
|--------|------------|
| `Registry` | реестр документов, целостность метаданных, ацикличность зависимостей, учёт отсутствующих документов |
| `Graph` | корпус как экземпляр `Polymath.KnowledgeGraph` |
| `Systems` | STEP-001: система, метрика, ресурс, накопление, воспроизводство, инвариант роста |
| `Uncertainty` | STEP-005: энтропия конфигурации, релевантность, редукция неопределённости, шумовой порог |
| `Complexity` | STEP-006: высвобожденный ресурс, условие появления уровня, каскад сложности |
-/
import RequestProject.AtlasKO.Registry
import RequestProject.AtlasKO.Graph
import RequestProject.AtlasKO.Systems
import RequestProject.AtlasKO.Uncertainty
import RequestProject.AtlasKO.Complexity
