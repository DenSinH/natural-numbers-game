FROM python:3.9-buster
WORKDIR /app

COPY requirements.txt .
RUN pip install -r requirements.txt

COPY . .

RUN apt-get update && apt-get install -y coq

WORKDIR webapp/coq
RUN make_vo.sh

WORKDIR ../
CMD ["python", "app.py"]