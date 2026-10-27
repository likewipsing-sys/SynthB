한빛 WT-1 — 오프라인 웨이브테이블 신디사이저 (PWA)

이 폴더를 HTTPS 웹 호스팅에 그대로 올리면 아이패드 홈 화면 앱이 됩니다.

1) 호스팅 (택1, 모두 무료)
   • GitHub Pages: 새 저장소 → 이 폴더의 파일을 모두 업로드 → Settings › Pages › Branch: main / root → 저장.
     잠시 뒤 https://<아이디>.github.io/<저장소>/ 주소가 생겨요. (아이패드 Safari에서도 업로드 가능)
   • Netlify Drop: 컴퓨터 브라우저에서 app.netlify.com/drop 에 이 폴더를 끌어다 놓기.
   • Cloudflare Pages: Workers & Pages › Create › Pages › Upload assets.
2) 아이패드 Safari로 그 주소를 열고, 공유 버튼 › 홈 화면에 추가.
3) 홈 화면 아이콘으로 한 번 실행하면 앱 전체가 캐시돼서 이후에는 비행기 모드에서도 실행돼요.

파일
  index.html            앱 전체 (UI + 오디오 엔진 내장)
  engine.js             오디오 엔진 (AudioWorklet)
  sw.js                 오프라인 캐시 (서비스 워커)
  manifest.webmanifest  홈 화면 앱 정보
  icons/                앱 아이콘

주의: index.html을 파일로 직접 열면(file://) 오프라인 캐시와 홈 화면 앱이 동작하지 않아요. 반드시 https 주소로 여세요.
