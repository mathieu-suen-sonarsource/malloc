node {
  stage('SCM') {
    checkout scm
  }
  stage('Download Build Wrapper') {
    sh "mkdir -p .sonar"
    sh "curl -sSLo build-wrapper-linux-x86.zip https://example.org/static/cpp/build-wrapper-linux-x86.zip"
    sh "unzip -o build-wrapper-linux-x86.zip -d .sonar"
  }
  stage('Build') {
    sh ".sonar/build-wrapper-linux-x86/build-wrapper-linux-x86-64 --out-dir bw-output make mdriver"
  }
  stage('SonarQube Analysis') {
    def scannerHome = tool 'SonarScanner';
    withSonarQubeEnv() {
      sh "${scannerHome}/bin/sonar-scanner -Dsonar.cfamily.build-wrapper-output=bw-output"
    }
  }
}
