; 캘린더 위젯 설치 파일 (Inno Setup 6)
; 만드는 법: ISCC.exe /DMyAppVersion=2.0.0 installer\CalendarWidget.iss
; 보통은 GitHub에서 릴리스를 만들면 자동으로 만들어져요 (.github\workflows\release.yml).

#ifndef MyAppVersion
  #define MyAppVersion "2.0.0"
#endif
#define MyAppName "캘린더 위젯"
#define MyAppExeName "CalendarWidget.exe"

[Setup]
; AppId는 한 번 정하면 바꾸지 마세요. 바꾸면 업데이트가 아니라 다른 프로그램으로 설치돼요.
AppId={{6B1C9A52-3E7D-4F8B-9C21-5A0E7D4B2F13}
AppName={#MyAppName}
AppVersion={#MyAppVersion}
AppVerName={#MyAppName} {#MyAppVersion}
AppPublisher=캘린더 위젯
VersionInfoVersion={#MyAppVersion}
; 관리자 권한 없이 사용자 폴더에 설치해요 (학교 PC에서도 설치할 수 있게)
PrivilegesRequired=lowest
DefaultDirName={localappdata}\Programs\CalendarWidget
DisableDirPage=yes
DisableProgramGroupPage=yes
DisableReadyPage=yes
OutputDir=Output
OutputBaseFilename=CalendarWidget-Setup-{#MyAppVersion}
SetupIconFile=..\assets\icon.ico
UninstallDisplayIcon={app}\{#MyAppExeName}
UninstallDisplayName={#MyAppName}
Compression=lzma2
SolidCompression=yes
WizardStyle=modern
; 업데이트할 때 켜져 있는 위젯을 닫고 바꿔요
CloseApplications=yes
RestartApplications=no
UsePreviousTasks=yes

[Languages]
#if FileExists(AddBackslash(CompilerPath) + "Languages\Korean.isl")
Name: "korean"; MessagesFile: "compiler:Languages\Korean.isl"
#else
Name: "english"; MessagesFile: "compiler:Default.isl"
#endif

[Tasks]
Name: "desktopicon"; Description: "바탕화면에 바로 가기 만들기"; Flags: unchecked

[Files]
Source: "..\dist\CalendarWidget\*"; DestDir: "{app}"; Flags: ignoreversion recursesubdirs createallsubdirs

[InstallDelete]
; 예전 버전의 부품이 남아 섞이지 않게 지우고 새로 깔아요
Type: filesandordirs; Name: "{app}\_internal"

[Icons]
Name: "{autoprograms}\{#MyAppName}"; Filename: "{app}\{#MyAppExeName}"
Name: "{autodesktop}\{#MyAppName}"; Filename: "{app}\{#MyAppExeName}"; Tasks: desktopicon

[Registry]
; 자동 실행은 위젯이 직접 켜고 꺼요. 지울 때 자동 실행 등록도 함께 지워요.
Root: HKCU; Subkey: "Software\Microsoft\Windows\CurrentVersion\Run"; ValueType: none; ValueName: "CalendarWidget"; Flags: uninsdeletevalue

[Run]
; 설치가 끝나면 위젯을 켜요. 자동 업데이트(조용히 설치)일 때도 다시 켜져요.
Filename: "{app}\{#MyAppExeName}"; Description: "캘린더 위젯 실행"; Flags: nowait postinstall

[UninstallDelete]
Type: filesandordirs; Name: "{app}"
