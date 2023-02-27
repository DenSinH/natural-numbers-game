docker image build -t natural-numbers-game
docker run -dp 80:80 --env-file .env natural-numbers-game