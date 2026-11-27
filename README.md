# 캘린더 위젯

아이폰 기본 캘린더(Google · iCloud)의 일정을 윈도우 바탕화면 전체에 펼쳐 보여 주는 위젯이에요.
여러 주 달력, 시간표, 할 일, 일정 알림, 컴퓨터를 켤 때 오늘 요약, 학사일정 파일(한글 · PDF · 엑셀) 가져오기가 있어요.

## 문서

| 문서 | 누구를 위한 | 내용 |
|---|---|---|
| [사용_설명서.md](사용_설명서.md) | 설치해서 쓰는 사람 | 설치, Google 로그인, 사용법, 설정, 업데이트 |
| [배포_가이드.md](배포_가이드.md) | 나눠 주는 사람 | Google 로그인 설정, GitHub에서 설치 파일 만들기, 새 버전 내기 |
| [개인정보처리방침_예시.md](개인정보처리방침_예시.md) | 나눠 주는 사람 | Google 검토 신청에 쓸 개인정보처리방침 예시 |

## 파일 구성

| 파일 | 하는 일 |
|---|---|
| calendar_widget.py | 위젯 프로그램 |
| requirements.txt | 필요한 파이썬 패키지 |
| assets/icon.ico | 프로그램 아이콘 |
| installer/CalendarWidget.iss | 설치 파일 설계도 (Inno Setup) |
| .github/workflows/release.yml | 릴리스를 만들면 설치 파일을 자동으로 만들어 붙이는 설정 |
| build_installer.bat | 내 컴퓨터에서 설치 파일 만들기 (Inno Setup 필요) |
| build_secrets.example.json | 내 컴퓨터에서 만들 때 쓰는 설정 예시 |
| tools/make_build_info.py | 설정 값을 프로그램에 넣는 도우미 |
| run.bat | 개발용 실행 (파이썬 필요) |

## 개발용으로 실행하기

파이썬 3.10 이상이 있으면 `run.bat`을 더블클릭해서 바로 실행할 수 있어요.
설치 파일 없이 실행하면 Google 로그인 정보가 들어 있지 않아서, 예전 방식인 '연결 코드'(Apps Script)로 Google 캘린더를 연결해요.
Google 로그인으로 시험해 보려면 환경 변수 `CW_GOOGLE_CLIENT_ID`, `CW_GOOGLE_CLIENT_SECRET`을 넣고 실행하면 돼요.

## 글꼴

위젯 화면에는 경기도가 무료로 배포하는 **경기천년체**(경기천년제목 Bold · Medium · Light, 경기천년바탕 Regular)를 넣어 썼어요.
글꼴 파일은 `assets/fonts`에 있고, 저작권은 경기도에 있어요. 다시 나눠 줄 때는 경기도의 경기천년체 사용 안내를 따라 주세요.
