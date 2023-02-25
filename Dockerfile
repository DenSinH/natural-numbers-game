FROM python:3.9-buster
WORKDIR /app

COPY requirements.txt .
RUN pip install -r requirements.txt

COPY . .

RUN apt-get update && apt-get install -y coq

WORKDIR webapp
CMD ["python", "app.py"]