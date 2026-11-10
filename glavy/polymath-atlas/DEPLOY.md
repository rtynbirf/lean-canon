# 🚀 DEPLOY — имперский деплой за 10 минут

> **Железное правило этого репозитория:** токены никогда не пишутся в файлы,
> в URL remote и в команды вида `https://TOKEN@github.com/...`. Только
> `gh auth login` или Git Credential Manager. Никаких исключений.

---

## 0. Безопасность (обязательно, 2 минуты)

1. Отозвать все токены, которые раньше вставлялись в чаты/файлы:
   **GitHub → Settings → Developer settings → Personal access tokens → удалить.**
2. Создать новый токен с минимальными правами:
   - классический (Classic): scope `repo` + `workflow` — этого достаточно;
   - или fine-grained: только нужный репозиторий, `Contents: Read and write`, `Workflows: Read and write`, `Pages: Read and write`.
3. Токен никому не пересылать — вводить только интерактивно при пуше.

## 1. Создать репозиторий на GitHub (2 минуты)

1. github.com → **New repository**
2. Name: `polymath-atlas` · Public · **без** README/LICENSE/.gitignore (они уже здесь)
3. Create

## 2. Запушить локальную копию (3 минуты)

В папке этого репозитория:

```bash
git init -b main
git add -A
git commit -m "Documentum Imperiale — initial imperial deployment"
git remote add origin https://github.com/rtynbirf/polymath-atlas.git
git push -u origin main
```

При пуше GitHub спросит логин и пароль — **в поле пароля вставьте токен**
(Git сохранит его в системный credential manager, не в файлы репозитория).

Альтернатива без токенов вообще:

```bash
gh auth login          # браузерная авторизация
gh repo create polymath-atlas --public --source=. --push
```

## 3. Включить витрину GitHub Pages (1 минута)

`Settings → Pages → Build and deployment → Source: GitHub Actions`
Workflow `.github/workflows/pages.yml` уже настроен: архив откроется на

```
https://rtynbirf.github.io/polymath-atlas/
```

## 4. Поставить имперский social preview (1 минута)

`Settings → General → Social preview → Edit → Upload`
файл `assets/social-preview.png` (1280×640, уже готов).

## 5. Поправить ссылку бейджа в архиве (30 секунд)

В `docs/index.html` заменить `OWNER` на свой логин:

```bash
sed -i 's|github.com/rtynbirf/polymath-atlas|github.com/rtynbirf/polymath-atlas|' docs/index.html
git add docs/index.html && git commit -m "badge: repo link" && git push
```

## 6. Подключить Lean-формализацию (когда будете готовы)

```bash
# скопировать папку Gestalt/ рядом с Lakefile
cp -r /путь/к/RequestProject/Gestalt ./Gestalt
# создать корневые файлы проекта Lean (если ещё нет)
echo "leanprover/lean4:stable" > lean-toolchain
git add Gestalt lean-toolchain && git commit -m "Gestalt: 7 modules, zero sorry" && git push
```

CI `.github/workflows/lean.yml` сам запустит `lean-action` и проверит,
что `sorry` в исходниках нет — стандарт Documentum Imperiale.

## ✅ Чек-лист готовности

- [ ] старые токены отозваны
- [ ] репозиторий создан, push прошёл
- [ ] Pages включён, архив открывается
- [ ] social preview поставлен
- [ ] ссылка бейджа поправлена
- [ ] Gestalt/ подключён, CI зелёный

**Documentum Imperiale** · *Ex Palimpsesto Imperiale*
